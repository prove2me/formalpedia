-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_dir
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:19.991468+00:00
-- url     : https://prove2.me/submissions/71d728f2-e31b-4810-a5dd-c97ed7533cd0

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_holo_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wir_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wir_hasLineDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {d : ℕ} (β t : ℂ) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {b : (Fin d → ℂ) → V} (hb : ContDiff ℝ 1 b) (hc : HasCompactSupport b) (hsupp : tsupport b ⊆ Ω)
    (v : Fin d → ℂ) :
    Integrable (fun x => psi β (g x / t) • fderiv ℝ b x v) (volume : Measure (Fin d → ℂ)) ∧
    Integrable (fun x => (psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) • b x)
      (volume : Measure (Fin d → ℂ)) ∧
    ∫ x, psi β (g x / t) • fderiv ℝ b x v =
      -∫ x, (psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) • b x := by
  have hgc : ContinuousOn g Ω := hg.continuousOn
  have hψ : ContinuousOn (fun x => psi β (g x / t)) Ω := by
    unfold psi
    fun_prop
  have hg1 : ContDiffOn ℂ 1 g Ω := by exact_mod_cast holo_contDiffOn hΩ hg 1
  have hdg : ContinuousOn (fun x => fderiv ℂ g x v) Ω := by
    have := hg1.continuousOn_fderiv_of_isOpen hΩ le_rfl
    exact this.clm_apply continuousOn_const
  have hψ' : ContinuousOn
      (fun x => psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) Ω := by
    refine hψ.mul (continuousOn_const.mul ?_)
    exact Complex.continuous_ofReal.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hdg))
  have hdb : Continuous (fun x => fderiv ℝ b x v) :=
    (hb.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdbc : HasCompactSupport (fun x => fderiv ℝ b x v) := hc.fderiv_apply (𝕜 := ℝ) v
  have hdbs : tsupport (fun x => fderiv ℝ b x v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hsupp
  have i1 := wir_integrable hΩ hψ hdb hdbc hdbs
  have i2 := wir_integrable hΩ hψ' hb.continuous hc hsupp
  have i3 := wir_integrable hΩ hψ hb.continuous hc hsupp
  refine ⟨i1, i2, ?_⟩
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin d → ℂ))) (B := ContinuousLinearMap.lsmul ℝ ℂ)
    (f := fun x => psi β (g x / t))
    (f' := fun x => psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ)))
    (g := b) (g' := fun x => fderiv ℝ b x v) (v := v) i2 i1 i3
    (fun x hx => wir_hasLineDerivAt β t ((hg x (hsupp hx)).differentiableAt (hΩ.mem_nhds (hsupp hx))) v)
    (fun x _ => ((hb.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v)
  exact key
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
