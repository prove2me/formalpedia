-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.fderiv_uu_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:36.561943+00:00
-- url     : https://prove2.me/submissions/83f6580d-7c51-44e5-8683-653e65574140

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtBrReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_ug
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_exists_br
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_exp_br
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_isOpen_An
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_ne_zero_of_An
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_om_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_uu_eq_br


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) {ζ : ℂ} (hζ : ζ ∈ An TT) (v : ℂ) :
    fderiv ℝ (uu TT α) ζ v = uu TT α ζ * (I * ((2 * (α ζ * v).im : ℝ) : ℂ)) := by
  have hne := ne_zero_of_An hTT hζ
  obtain ⟨s, hs⟩ := exists_br hne
  have hev : uu TT α =ᶠ[𝓝 ζ] ug TT α s := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hu : ug TT α s ζ = uu TT α ζ := (uu_eq_br hTT hα hcurv hhol s hζ).symm
  rw [hev.fderiv_eq, (hasFDerivAt_ug hTT hα hcurv s hs hζ).fderiv]
  have hb : α ζ * ζ * (ζ⁻¹ * v) = α ζ * v := by field_simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, om_apply, bet, exp_br s hne,
    smul_eq_mul, hu, hb]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
