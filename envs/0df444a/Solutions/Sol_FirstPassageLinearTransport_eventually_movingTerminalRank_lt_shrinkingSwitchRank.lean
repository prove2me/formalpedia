-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_movingTerminalRank_lt_shrinkingSwitchRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:20:24.0437+00:00
-- url     : https://prove2.me/submissions/38ac6903-ee40-492d-8a97-6f8c31dff491

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_eventually_polylogTerminalRank_lt_shrinkingSwitchRank


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℕ → ℝ} {Amax C : ℝ}
    (hAmax : 0 ≤ Amax) (hAC : Amax / Real.log 2 < C)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop,
      movingTerminalRank A M < shrinkingSwitchRank C M := by
  have hFixed := eventually_polylogTerminalRank_lt_shrinkingSwitchRank
    hAmax hAC
  filter_upwards [hUpper, hFixed] with M hAM hFixed
  have hlogb0 : 0 ≤ Real.logb 2 ((M : ℝ) + 2) := by
    apply Real.logb_nonneg (by norm_num)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hceil : movingTerminalRank A M ≤ polylogTerminalRank Amax M := by
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_right hAM hlogb0)
  exact hceil.trans_lt hFixed
end FirstPassageLinearTransport
