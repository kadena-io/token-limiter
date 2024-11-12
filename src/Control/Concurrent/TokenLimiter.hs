{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}

-- | Fast rate-limiting via token bucket algorithm. Uses lock-free
-- compare-and-swap operations on the fast path when debiting tokens.
module Control.Concurrent.TokenLimiter
  ( Count,
    LimitConfig (..),
    RateLimiter,
    newRateLimiter,
    tryDebit,
    penalize,
    waitDebit,
    defaultLimitConfig,
  )
where

import "base" Control.Concurrent (MVar, modifyMVar, newMVar, readMVar, threadDelay)
import "base" Data.IORef (newIORef, readIORef, writeIORef)
import "base" GHC.Exts (Int (..), RealWorld, casIntArray#)
import "base" GHC.Generics (Generic)
import "base" GHC.IO (IO (..))
import "clock" System.Clock (Clock (..), TimeSpec, fromNanoSecs, getTime, toNanoSecs)
import "primitive" Data.Primitive.PrimArray (MutablePrimArray (..), newPrimArray, readPrimArray, writePrimArray)
import "primitive" Data.Primitive.Types (sizeOf)

type Count = Int

casIntArray :: MutablePrimArray RealWorld Int -> Int -> Int -> Int -> IO Int
casIntArray (MutablePrimArray marr#) (I# a#) (I# b#) (I# c#) =
  IO $ \s0# -> case casIntArray# marr# a# b# c# s0# of
    (# s1#, i# #) -> (# s1#, I# i# #)

data LimitConfig = LimitConfig
  { -- | maximum number of tokens the bucket can hold at any one time.
    maxBucketTokens :: {-# UNPACK #-} !Count,
    -- | how many tokens should be in the bucket when it's created.
    initialBucketTokens :: {-# UNPACK #-} !Count,
    -- | how many tokens should replenish the bucket per second.
    bucketRefillTokensPerSecond :: {-# UNPACK #-} !Count,
    -- | clock action, 'defaultLimitConfig' uses the monotonic system clock.
    -- Mostly provided for mocking in the testsuite.
    clockAction :: IO TimeSpec,
    -- | action to delay for the given time interval. 'defaultLimitConfig'
    -- forwards to 'threadDelay'. Provided for mocking.
    delayAction :: TimeSpec -> IO ()
  }
  deriving stock (Generic)

defaultLimitConfig :: LimitConfig
defaultLimitConfig = LimitConfig 5 1 1 nowIO sleepIO
  where
    nowIO = getTime Monotonic
    sleepIO x = threadDelay $! fromInteger (toNanoSecs x `div` 1000)

data RateLimiter = RateLimiter
  { bucketTokens :: {-# UNPACK #-} !(MutablePrimArray RealWorld Int),
    bucketLastServiced :: {-# UNPACK #-} !(MVar TimeSpec)
  }

newRateLimiter :: LimitConfig -> IO RateLimiter
newRateLimiter lc = do
  now <- lc.clockAction
  lastServiced <- newMVar now
  let initial = lc.initialBucketTokens
  arr <- newPrimArray @_ @Int (sizeOf initial)
  writePrimArray arr 0 initial
  pure $
    RateLimiter
      { bucketTokens = arr,
        bucketLastServiced = lastServiced
      }

rateToNsPer :: (Integral a) => a -> a
rateToNsPer tps = 1_000_000_000 `div` tps

readBucket :: MutablePrimArray RealWorld Int -> IO Int
readBucket bucket = readPrimArray bucket 0

-- | Unconditionally debit this amount of tokens from the rate limiter, driving
-- it negative if necessary. Returns the new bucket balance.
--
-- /Since: 0.2/
penalize :: RateLimiter -> Count -> IO Count
penalize rl delta = addLoop
  where
    addLoop = do
      x <- readBucket rl.bucketTokens
      let x' = x - delta
      prev <- casIntArray rl.bucketTokens 0 x x'
      if prev == x
        then pure x'
        else addLoop

-- | Attempt to pull the given number of tokens from the bucket. Returns 'True'
-- if the tokens were successfully debited.
tryDebit :: LimitConfig -> RateLimiter -> Count -> IO Bool
tryDebit cfg rl cnt = do
  let nowIO = cfg.clockAction
  snd <$> tryDebit' nowIO cfg rl cnt

tryDebit' :: IO TimeSpec -> LimitConfig -> RateLimiter -> Count -> IO (Int, Bool)
tryDebit' nowIO cfg rl ndebits = tryGrab
  where
    tryGrab = do
      !nt <- readBucket rl.bucketTokens
      if nt >= ndebits
        then tryCas nt (nt - ndebits)
        else fetchMore nt

    -- tryCas :: Int -> Int -> IO (Int, Bool)
    tryCas nt newVal = do
      prevV <- casIntArray rl.bucketTokens 0 nt newVal
      if prevV == nt
        then pure (newVal, True)
        else tryGrab

    addLoop !numNewTokens = go
      where
        go = do
          b <- readBucket rl.bucketTokens
          let b' = min (fromIntegral cfg.maxBucketTokens) (b + numNewTokens)
          prev <- casIntArray rl.bucketTokens 0 b b'
          if prev == b
            then pure b'
            else go

    fetchMore !nt = do
      newBalance <- modifyMVar rl.bucketLastServiced $ \lastUpdated -> do
        now <- nowIO
        let !numNanos = toNanoSecs $ now - lastUpdated
        let !nanosPerToken = toInteger $ rateToNsPer cfg.bucketRefillTokensPerSecond
        let !numNewTokens0 = numNanos `div` nanosPerToken
        let numNewTokens = fromIntegral numNewTokens0
        let !lastUpdated' =
              lastUpdated
                + fromNanoSecs (toInteger numNewTokens * toInteger nanosPerToken)
        if numNewTokens > 0
          then do
            nb <- addLoop numNewTokens
            return (lastUpdated', nb)
          else return (lastUpdated, nt)
      if newBalance >= ndebits
        then tryGrab
        else return (newBalance, False)

waitForTokens :: TimeSpec -> LimitConfig -> RateLimiter -> Count -> Count -> IO ()
waitForTokens now cfg (RateLimiter _ mv) balance ntokens = do
  lastUpdated <- readMVar mv
  let numNeeded = fromIntegral ntokens - balance
  let delta = toNanoSecs $ now - lastUpdated
  let nanos = nanosPerToken * toInteger numNeeded
  let sleepNanos = max 1 (fromInteger (nanos - delta + 500))
  let !sleepSpec = fromNanoSecs sleepNanos
  sleepFor sleepSpec
  where
    nanosPerToken = toInteger $ rateToNsPer refillRate
    refillRate = bucketRefillTokensPerSecond cfg
    sleepFor = delayAction cfg

-- | Attempt to pull /k/ tokens from the bucket, sleeping in a loop until they
-- become available. Will not partially fulfill token requests (i.e. it loops
-- until the entire allotment is available in one swoop), and makes no attempt
-- at fairness or queueing (i.e. you will probably get \"thundering herd\" on
-- wakeup if a number of threads are contending for fresh tokens).
waitDebit :: LimitConfig -> RateLimiter -> Count -> IO ()
waitDebit lc rl ndebits = go
  where
    cacheClock ref = do
      m <- readIORef ref
      case m of
        Nothing -> do
          !now <- clockAction lc
          writeIORef ref (Just now)
          return now
        Just t -> return t
    go = do
      ref <- newIORef Nothing
      let clock = cacheClock ref
      (balance, b) <- tryDebit' clock lc rl ndebits
      if b
        then do
          return ()
        else do
          now <- clock
          waitForTokens now lc rl balance ndebits >> go
