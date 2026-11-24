-- Prove2me | solution 1 for DeletedPrimes.abs_muS_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:58:01.591678+00:00
-- url     : https://prove2.me/submissions/9fd0814d-e61a-4882-84a8-be3a99aa19c9

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_muS_ne_zero_iff

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (d : ℕ) : |(muS S d : ℝ)| = if muS S d = 0 then 0 else 1 := by
  split_ifs with h
  · simp [h]
  · have hsq := (muS_ne_zero_iff.mp h).1
    have : muS S d = ArithmeticFunction.moebius d := by
      unfold muS; rw [if_pos (muS_ne_zero_iff.mp h).2]
    rw [this, ← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsq, Int.cast_one]
end DeletedPrimes
