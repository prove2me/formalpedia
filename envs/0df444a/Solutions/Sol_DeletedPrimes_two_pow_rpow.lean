-- Prove2me | solution 1 for DeletedPrimes.two_pow_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:54:54.074246+00:00
-- url     : https://prove2.me/submissions/b0e6b2c8-6de8-4cec-a88b-ead4ceb3cc36

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (j : ℕ) (a : ℝ) : ((2 : ℝ) ^ j) ^ a = ((2 : ℝ) ^ a) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]
end DeletedPrimes
