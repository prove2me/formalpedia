-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_genuine_Qp_pathwise_volume_ae_reward_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:16:05.826+00:00
-- url     : https://prove2.me/submissions/8871c1c3-6281-4abf-ae7b-98787097cb71

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual real-clock terminal Esscher path-clock law preserves every
original pathwise Lebesgue-a.e. reward equality; no tilted infinite-path law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (F G : Ω × ℝ → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G)
    (hFG : ∀ ω : Ω, ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
      F (ω, r) = G (ω, r)) :
    (∫⁻ z : Ω × ℝ, F z ∂
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    (∫⁻ z : Ω × ℝ, G z ∂
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) := by
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  let D : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))
  have hD : Measurable D :=
    chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
      X θ (chat04_levy_joint_time_state_measurable X)
  have hFD : Measurable (fun z : Ω × ℝ => D z * F z) :=
    hD.mul hF
  have hGD : Measurable (fun z : Ω × ℝ => D z * G z) :=
    hD.mul hG
  have hPDF : Measurable (exponentialPDF p) :=
    (measurable_exponentialPDFReal p).ennreal_ofReal
  have hFI (ω : Ω) : Measurable (fun r : ℝ => D (ω, r) * F (ω, r)) :=
    hFD.comp (measurable_const.prodMk measurable_id)
  have hGI (ω : Ω) : Measurable (fun r : ℝ => D (ω, r) * G (ω, r)) :=
    hGD.comp (measurable_const.prodMk measurable_id)
  have hInner (ω : Ω) :
      (∫⁻ r : ℝ, D (ω, r) * F (ω, r) ∂(expMeasure p)) =
      (∫⁻ r : ℝ, D (ω, r) * G (ω, r) ∂(expMeasure p)) := by
    change (∫⁻ r : ℝ, D (ω, r) * F (ω, r)
        ∂(volume.withDensity (exponentialPDF p))) =
      (∫⁻ r : ℝ, D (ω, r) * G (ω, r)
        ∂(volume.withDensity (exponentialPDF p)))
    rw [lintegral_withDensity_eq_lintegral_mul volume hPDF (hFI ω),
      lintegral_withDensity_eq_lintegral_mul volume hPDF (hGI ω)]
    apply lintegral_congr_ae
    filter_upwards [hFG ω] with r hr
    simpa only [Pi.mul_apply, hr]
  change (∫⁻ z : Ω × ℝ, F z
      ∂((P.prod (expMeasure p)).withDensity D)) =
    (∫⁻ z : Ω × ℝ, G z
      ∂((P.prod (expMeasure p)).withDensity D))
  calc
    _ = ∫⁻ z : Ω × ℝ, D z * F z ∂(P.prod (expMeasure p)) := by
      rw [lintegral_withDensity_eq_lintegral_mul]
      · simp only [Pi.mul_apply]
      · exact hD
      · exact hF
    _ = ∫⁻ ω : Ω, ∫⁻ r : ℝ, D (ω,r) * F (ω,r)
        ∂(expMeasure p) ∂P :=
      lintegral_prod _ hFD.aemeasurable
    _ = ∫⁻ ω : Ω, ∫⁻ r : ℝ, D (ω,r) * G (ω,r)
        ∂(expMeasure p) ∂P := by
      apply lintegral_congr
      intro ω
      exact hInner ω
    _ = ∫⁻ z : Ω × ℝ, D z * G z ∂(P.prod (expMeasure p)) :=
      (lintegral_prod _ hGD.aemeasurable).symm
    _ = _ := by
      rw [lintegral_withDensity_eq_lintegral_mul]
      · simp only [Pi.mul_apply]
      · exact hD
      · exact hG
