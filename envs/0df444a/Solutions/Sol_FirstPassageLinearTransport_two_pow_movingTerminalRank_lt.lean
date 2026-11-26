-- Prove2me | solution 1 for FirstPassageLinearTransport.two_pow_movingTerminalRank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:38:09.860421+00:00
-- url     : https://prove2.me/submissions/8c5c7cb7-1974-4c55-8c60-7d8d1ee060c2

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_movingTerminalRank_lt_add_one

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℕ → ℝ} {M : ℕ} (hA : 0 ≤ A M) :
    ((2 ^ movingTerminalRank A M : ℕ) : ℝ) <
      2 * (((M : ℝ) + 2) ^ (A M)) := by
  have hx : 0 < (M : ℝ) + 2 := by positivity
  have hExp := movingTerminalRank_lt_add_one hA
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  calc
    (2 : ℝ) ^ (movingTerminalRank A M : ℝ) <
        (2 : ℝ) ^ (A M * Real.logb 2 ((M : ℝ) + 2) + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hExp
    _ = 2 * (((M : ℝ) + 2) ^ (A M)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
      rw [show A M * Real.logb 2 ((M : ℝ) + 2) =
          Real.logb 2 ((M : ℝ) + 2) * A M by ring]
      rw [Real.rpow_mul (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) hx]
      ring
end FirstPassageLinearTransport
