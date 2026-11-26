-- Prove2me | solution 1 for FirstPassageLinearTransport.movingTerminalRank_lt_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:36:54.365715+00:00
-- url     : https://prove2.me/submissions/f02b7274-adfc-4b6d-add3-1ea95b68fd0b

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℕ → ℝ} {M : ℕ} (hA : 0 ≤ A M) :
    (movingTerminalRank A M : ℝ) <
      A M * Real.logb 2 ((M : ℝ) + 2) + 1 := by
  apply Nat.ceil_lt_add_one
  have hx : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  exact mul_nonneg hA (Real.logb_nonneg (by norm_num) hx)
end FirstPassageLinearTransport
