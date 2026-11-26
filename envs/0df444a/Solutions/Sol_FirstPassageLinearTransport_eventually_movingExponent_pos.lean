-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_movingExponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:45.467078+00:00
-- url     : https://prove2.me/submissions/b2fea592-2203-4d32-a194-ee0a190faab4

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingTerminalRank_atTop

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, 0 < A M := by
  have hRank := (tendsto_atTop.1
    (tendsto_movingTerminalRank_atTop hbuffer)) 1
  filter_upwards [hRank] with M hRank
  have hceil : 0 < A M * Real.logb 2 ((M : ℝ) + 2) :=
    Nat.ceil_pos.mp (show 0 < movingTerminalRank A M by omega)
  have hlogb : 0 < Real.logb 2 ((M : ℝ) + 2) := by
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  nlinarith
end FirstPassageLinearTransport
