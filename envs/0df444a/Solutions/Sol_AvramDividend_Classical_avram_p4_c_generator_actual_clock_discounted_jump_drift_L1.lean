-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_actual_clock_discounted_jump_drift_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:59:31.377649+00:00
-- url     : https://prove2.me/submissions/e373f0ca-ee68-4dd4-bbf7-773c8faf2217

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_actual_clock_jump_drift_L1_indicator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Discounted original source nonlinear generator drift is L¹ at the
actual predictable prepayment reserve and ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : ∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
      Measurable[𝓕.rightCont.predictable] f →
      (∫⁻ p, f p ∂μ) =
        (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)))
    (q : ℝ) (hq : 0 ≤ q)
    (hclock : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => (p.1 : ℝ))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let A : Set (ℝ≥0 × Ω) :=
      {p | (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧ Y p ∈ Icc (u + δ) v}
    Integrable (A.indicator (fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (∫ z in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν))) μ := by
  intro Y A
  have hBase :=
    avram_p4_c_generator_actual_clock_jump_drift_L1_indicator
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv T μ hμ
  dsimp at hBase
  let a : ℝ≥0 × Ω → ℝ := fun p => Real.exp (-(q * (p.1 : ℝ)))
  have hameas : Measurable[𝓕.rightCont.predictable] a := by
    dsimp [a]
    fun_prop
  have habound : ∀ p : ℝ≥0 × Ω, |a p| ≤ (1 : ℝ) := by
    intro p
    change |Real.exp (-(q * (p.1 : ℝ)))| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    have ht : 0 ≤ (p.1 : ℝ) := p.1.property
    have hle : -(q * (p.1 : ℝ)) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg hq ht)
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  have hweighted : Integrable (fun p => a p *
      (A.indicator (fun p => ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν)) p) μ := by
    apply Integrable.bdd_mul hBase hameas.aestronglyMeasurable (c := 1)
    filter_upwards [] with p
    simpa only [Real.norm_eq_abs] using habound p
  have hEq : A.indicator (fun p => a p *
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν)) =
      (fun p => a p * A.indicator (fun p =>
        ∫ z in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν) p) := by
    funext p
    by_cases hp : p ∈ A
    · simp [Set.indicator, hp]
    · simp [Set.indicator, hp]
  change Integrable (A.indicator (fun p => a p *
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν))) μ
  rw [hEq]
  exact hweighted
