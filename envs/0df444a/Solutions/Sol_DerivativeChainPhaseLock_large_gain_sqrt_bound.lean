-- Prove2me | solution 1 for DerivativeChainPhaseLock.large_gain_sqrt_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:46:09.777952+00:00
-- url     : https://prove2.me/submissions/39c875ef-8fae-47c2-b899-de6f68a322ed

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option maxHeartbeats 1000000
open DerivativeChainPhaseLock

theorem solution (K v D : ℝ) (hK : 0 ≤ K) (hv : 0 ≤ v)
    (hvd : v ≤ D)
    (hgain : (K+1)*Real.sqrt v ≤ (K-1)*Real.sqrt D) :
    Real.sqrt (K*v)+Real.sqrt (D-v) ≤ Real.sqrt (K*D) := by
  have hD : 0 ≤ D := hv.trans hvd
  have hs : 0 ≤ Real.sqrt D-Real.sqrt v := sub_nonneg.mpr (Real.sqrt_le_sqrt hvd)
  have hg : 0 ≤ (K-1)*Real.sqrt D-(K+1)*Real.sqrt v := sub_nonneg.mpr hgain
  have hfact := mul_nonneg hs hg
  have hsquare : D-v ≤ (Real.sqrt K*(Real.sqrt D-Real.sqrt v))^2 := by
    rw [mul_pow,Real.sq_sqrt hK]
    nlinarith only [hfact,Real.sq_sqrt hv,Real.sq_sqrt hD]
  have hdelta : Real.sqrt (D-v) ≤ Real.sqrt K*(Real.sqrt D-Real.sqrt v) :=
    (Real.sqrt_le_left (mul_nonneg (Real.sqrt_nonneg _) hs)).mpr hsquare
  calc
    Real.sqrt (K*v)+Real.sqrt (D-v) = Real.sqrt K*Real.sqrt v+Real.sqrt (D-v) := by
      rw [Real.sqrt_mul hK]
    _ ≤ Real.sqrt K*Real.sqrt v+Real.sqrt K*(Real.sqrt D-Real.sqrt v) :=
      add_le_add (le_refl _) hdelta
    _ = Real.sqrt (K*D) := by rw [Real.sqrt_mul hK]; ring
