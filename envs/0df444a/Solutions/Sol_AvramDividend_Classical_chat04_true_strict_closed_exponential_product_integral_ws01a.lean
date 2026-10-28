-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_strict_closed_exponential_product_integral_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:33:11.256978+00:00
-- url     : https://prove2.me/submissions/3f7298a4-8c4d-4cc1-8466-369247947758

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_killed_closed_history_ae_time_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

/-- Strict first-passage killing and full closed-history killing agree for
    any measurable nonnegative reward at the true independent clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) (x : ℝ)
    (R : Ω × ℝ → ℝ≥0∞) (hR : Measurable R) :
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator R z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}).indicator R z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) := by
  let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
    ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}
  let C : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
    ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
  have hE : MeasurableSet E :=
    chat04_exponential_clock_strict_lower_killing_joint_measurable X (-x)
  have hC : MeasurableSet C :=
    chat04_closed_history_lower_survival_joint_measurable_ws01a X x
  have hEI : Measurable (E.indicator R) := hR.indicator hE
  have hCI : Measurable (C.indicator R) := hR.indicator hC
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  have hPdf : Measurable (ProbabilityTheory.exponentialPDF p) :=
    (ProbabilityTheory.measurable_exponentialPDFReal p).ennreal_ofReal
  have hSliceE (ω : Ω) :
      Measurable (fun t : ℝ => E.indicator R (ω, t)) :=
    hEI.comp (measurable_const.prodMk measurable_id)
  have hSliceC (ω : Ω) :
      Measurable (fun t : ℝ => C.indicator R (ω, t)) :=
    hCI.comp (measurable_const.prodMk measurable_id)
  have hInner (ω : Ω) :
      (∫⁻ t : ℝ, E.indicator R (ω, t)
        ∂(ProbabilityTheory.expMeasure p)) =
      (∫⁻ t : ℝ, C.indicator R (ω, t)
        ∂(ProbabilityTheory.expMeasure p)) := by
    change (∫⁻ t : ℝ, E.indicator R (ω, t)
        ∂(volume.withDensity (ProbabilityTheory.exponentialPDF p))) =
      (∫⁻ t : ℝ, C.indicator R (ω, t)
        ∂(volume.withDensity (ProbabilityTheory.exponentialPDF p)))
    rw [lintegral_withDensity_eq_lintegral_mul volume hPdf (hSliceE ω),
        lintegral_withDensity_eq_lintegral_mul volume hPdf (hSliceC ω)]
    apply lintegral_congr_ae
    filter_upwards
      [chat04_strict_lower_killed_closed_history_ae_time_ws01a X (-x) ω]
      with t ht
    have ht' : (ω, t) ∈ E ↔ (ω, t) ∈ C := by
      simpa only [E, C, mem_setOf_eq] using ht
    by_cases hs : (ω, t) ∈ E
    · have hc := ht'.mp hs
      simp [Set.indicator, hs, hc]
    · have hc : (ω, t) ∉ C := fun hc => hs (ht'.mpr hc)
      simp [Set.indicator, hs, hc]
  change (∫⁻ z : Ω × ℝ, E.indicator R z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ z : Ω × ℝ, C.indicator R z
      ∂(P.prod (ProbabilityTheory.expMeasure p)))
  calc
    _ = ∫⁻ ω : Ω, ∫⁻ t : ℝ, E.indicator R (ω, t)
        ∂(ProbabilityTheory.expMeasure p) ∂P :=
      lintegral_prod (E.indicator R) hEI.aemeasurable
    _ = ∫⁻ ω : Ω, ∫⁻ t : ℝ, C.indicator R (ω, t)
        ∂(ProbabilityTheory.expMeasure p) ∂P := by
      apply lintegral_congr
      intro ω
      exact hInner ω
    _ = _ := (lintegral_prod (C.indicator R) hCI.aemeasurable).symm
