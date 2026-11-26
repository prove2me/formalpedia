-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_movingExponent_pos_of_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:33.70531+00:00
-- url     : https://prove2.me/submissions/474bc702-8ebd-4808-b5a1-866c05fcd781

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingTerminalRank_atTop_of_sharp

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, 0 < A M := by
  have hRank := (tendsto_atTop.1
    (tendsto_movingTerminalRank_atTop_of_sharp hbuffer)) 1
  filter_upwards [hRank] with M hRank
  have hceil : 0 < A M * Real.logb 2 ((M : ℝ) + 2) :=
    Nat.ceil_pos.mp (show 0 < movingTerminalRank A M by omega)
  have hlogb : 0 < Real.logb 2 ((M : ℝ) + 2) := by
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  nlinarith
end FirstPassageLinearTransport
