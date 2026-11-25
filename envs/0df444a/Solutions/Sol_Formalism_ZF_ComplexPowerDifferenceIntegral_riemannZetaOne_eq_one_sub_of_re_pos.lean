-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:14:53.535126+00:00
-- url     : https://prove2.me/submissions/4ccaae7b-86ef-4df3-952e-6c39c2b84633

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaOneEqOneSubOfRePos
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_one_lt_identity
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_Dz_differentiableOn


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
open Formalism.ZF.ComplexPowerDifferenceIntegral
namespace Formalism.ZF.ComplexPowerDifferenceIntegral
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) : riemannZeta₁ s = s - Dz s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hU
  have hG : AnalyticOnNhd ℂ (fun z => z - Dz z) {z : ℂ | 0 < z.re} :=
    (differentiableOn_id.sub Dz_differentiableOn).analyticOnNhd hU
  have heq : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] (fun z => z - Dz z) := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num at hz
    rw [← one_lt_identity hz]
    unfold riemannZeta₁ riemannZeta₀
    rw [if_neg hz1, mul_sub, mul_inv_cancel₀ (sub_ne_zero.mpr hz1)]
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num) heq hs
end Formalism.ZF.ComplexPowerDifferenceIntegral
