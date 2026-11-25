-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.smooth_extension_of_fourier_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:52.47448+00:00
-- url     : https://prove2.me/submissions/7c00925e-86c1-4619-a20f-74d3d296b90b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothBoundedOfFourierDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousExtensionOfFourierDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_unif_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_smooth_bounded_of_fourier_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_smooth_decay_of_weighted


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex Module
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hE : Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t))
    (hc : ∀ t, t ≠ 0 → ContinuousAt D t)
    (hdD : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3)))
    (hdE : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ t, t ≠ 0 → D' t = D t) ∧ (∫ t, D' t = ∫ t, D t) ∧
      (∃ C', ∀ j ≤ m, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ C' * (1 + ‖t‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D') ∧ ∫ t, iteratedFDeriv ℝ j D' t = 0 := by
  set E : ℂ → ℂ := fun t => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t with hEdef
  obtain ⟨D', hD'c, -, hD'eq⟩ := smooth_bounded_of_fourier_decay D m C hD hdD
  obtain ⟨E', hE'c, hE'b, hE'eq⟩ := smooth_bounded_of_fourier_decay E m C hE hdE
  have hEc : ∀ t, t ≠ 0 → ContinuousAt E t := fun t ht => by
    show ContinuousAt (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) t
    exact (((continuous_const.add (continuous_norm.pow 2)).pow 2).continuousAt).smul (hc t ht)
  have hw : ∀ x, E' x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x := by
    have hcont1 : Continuous E' := hE'c.continuous
    have hcont2 : Continuous (fun x : ℂ => ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x) :=
      ((continuous_const.add (continuous_norm.pow 2)).pow 2).smul hD'c.continuous
    have h := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hcont1 hcont2 (fun x hx => by
      have hx0 : x ≠ 0 := hx
      show E' x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D' x
      rw [hE'eq x (hEc x hx0), hD'eq x (hc x hx0)])
    exact fun x => congrFun h x
  obtain ⟨B, hB⟩ := unif_bound (fun j t => ‖iteratedFDeriv ℝ j E' t‖) m hE'b
  obtain ⟨-, hdec, hint⟩ := smooth_decay_of_weighted (V := ℂ) (by rw [Complex.finrank_real_complex]; norm_num) hE'c B hB hw
  have hae : D' =ᵐ[volume] D := by
    have : ∀ᵐ t ∂(volume : Measure ℂ), t ≠ 0 := by
      rw [ae_iff]; simpa using (measure_singleton (0 : ℂ))
    filter_upwards [this] with t ht
    exact hD'eq t (hc t ht)
  exact ⟨D', hD'c, fun t ht => hD'eq t (hc t ht), integral_congr_ae hae, hdec, hint⟩
end Formalism.FourierDecayAlt.P5.HerC.Fou
