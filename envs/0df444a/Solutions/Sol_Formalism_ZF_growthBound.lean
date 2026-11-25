-- Prove2me | solution 1 for Formalism.ZF.growthBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:12.372597+00:00
-- url     : https://prove2.me/submissions/589ac381-092c-49da-821e-9ac3de1f0993

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaOneEqOneSubOfRePos
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Theorems.Thm_Formalism_ZF_norm_Dz_le
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_riemannZetaOne_eq_one_sub_of_re_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : ZetaGrowth := by
  intro s hs hs1
  have h1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    unfold riemannZeta₁ riemannZeta₀
    rw [if_neg hs1, mul_sub, mul_inv_cancel₀ (sub_ne_zero.2 hs1)]
    ring
  have hD := norm_Dz_le hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hpos : 0 < ‖s - 1‖ := norm_pos_iff.2 hne
  have hz : riemannZeta s = (s - ComplexPowerDifferenceIntegral.Dz s) / (s - 1) := by
    rw [← ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hs, h1]
    field_simp
  rw [hz, norm_div, div_le_iff₀ hpos]
  have hs' : ‖s‖ ≤ ‖s - 1‖ + 1 := by simpa using norm_add_le (s - 1) 1
  calc ‖s - ComplexPowerDifferenceIntegral.Dz s‖ ≤ ‖s‖ + ‖ComplexPowerDifferenceIntegral.Dz s‖ := norm_sub_le _ _
    _ ≤ (‖s - 1‖ + 1) + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := add_le_add hs' hD
    _ = (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) * ‖s - 1‖ := by
        field_simp
end Formalism.ZF
