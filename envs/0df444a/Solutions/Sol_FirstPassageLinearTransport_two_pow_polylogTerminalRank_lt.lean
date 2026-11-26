-- Prove2me | solution 1 for FirstPassageLinearTransport.two_pow_polylogTerminalRank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:10.480378+00:00
-- url     : https://prove2.me/submissions/bc908833-3ca8-47d8-b216-745a5e0ad065

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Theorems.Thm_FirstPassageLinearTransport_polylogTerminalRank_lt_add_one

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℝ} (hA : 0 ≤ A) (M : ℕ) :
    ((2 ^ polylogTerminalRank A M : ℕ) : ℝ) <
      2 * (((M : ℝ) + 2) ^ A) := by
  have hx : 0 < (M : ℝ) + 2 := by positivity
  have hExp := polylogTerminalRank_lt_add_one hA M
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  calc
    (2 : ℝ) ^ (polylogTerminalRank A M : ℝ) <
        (2 : ℝ) ^
          (A * Real.logb 2 ((M : ℝ) + 2) + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hExp
    _ = 2 * (((M : ℝ) + 2) ^ A) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
      rw [show A * Real.logb 2 ((M : ℝ) + 2) =
          Real.logb 2 ((M : ℝ) + 2) * A by ring]
      rw [Real.rpow_mul (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) hx]
      ring
end FirstPassageLinearTransport
