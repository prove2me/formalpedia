-- Prove2me | solution 2 for AvramDividend.Classical.avram_chat24_bv_compact_finite_measure_generator_recombination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:52:05.894186+00:00
-- url     : https://prove2.me/submissions/fa83b971-ec68-4f7b-8312-bcb8a98b2464

import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_generator_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original BV generator reassembles under finite physical test measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (w : ℝ → ℝ) (hwm : Measurable w) (q a b L R A : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b, |w u - w v| ≤ L * |u - v|)
    (hW : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hDeriv : ∀ y ∈ Icc a b, |deriv w y| ≤ A)
    (hGen : ∀ y ∈ Icc a b, X.GeneratorIntegrable w y)
    {ι : Type*} [MeasurableSpace ι] (μ : Measure ι) [IsFiniteMeasure μ]
    (Y e : ι → ℝ) (hYm : Measurable Y) (hem : Measurable e)
    (he : ∀ t, |e t| ≤ 1) (E : Set ι) (hEm : MeasurableSet E)
    (hE : ∀ t ∈ E, Y t ∈ Icc a b) :
    (∫ t, if t ∈ E then e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0 ∂μ) =
      -(∫ t, if t ∈ E then e t * (∫ z in Iio (0 : ℝ),
        w (Y t + z) - w (Y t) ∂X.ν) else 0 ∂μ) +
      (∫ t, if t ∈ E then e t * (X.generator w (Y t) - q * w (Y t)) else 0 ∂μ) := by
  let f : ι → ℝ := fun t => if t ∈ E then e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0
  let g : ι → ℝ := fun t => if t ∈ E then e t * (∫ z in Iio (0 : ℝ), w (Y t + z) - w (Y t) ∂X.ν) else 0
  let j : ℝ → ℝ := fun y => ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν
  let B : ℝ := |X.drift| * A + |q| * R
  obtain ⟨K, hK0, hK⟩ := avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform X hBV w hwm q a b L R A ha ha2 hab hL hR hA hLip hW hDeriv
  have hfm : Measurable f := by
    apply Measurable.ite hEm
    · exact hem.mul ((measurable_const.mul ((measurable_deriv w).comp hYm)).sub (measurable_const.mul (hwm.comp hYm)))
    · exact measurable_const
  have hgm : Measurable g := by
    have hjm : Measurable j := avram_p3_e_compensator_original_negative_jump_generator_measurable X (avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite X) w hwm
    apply Measurable.ite hEm
    · exact hem.mul (hjm.comp hYm)
    · exact measurable_const
  have hraw : ∀ y ∈ Icc a b, |X.drift * deriv w y - q * w y| ≤ B := by
    intro y hy
    have hwy := hW y hy.2
    calc
      |X.drift * deriv w y - q * w y| ≤ |X.drift * deriv w y| + |q * w y| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (X.drift * deriv w y) (0 : ℝ) (q * w y))
      _ = |X.drift| * |deriv w y| + |q| * |w y| := by rw [abs_mul, abs_mul]
      _ ≤ B := add_le_add (mul_le_mul_of_nonneg_left (hDeriv y hy) (abs_nonneg _)) (mul_le_mul_of_nonneg_left hwy (abs_nonneg _))
  have hgraw : ∀ y ∈ Icc a b, |j y| ≤ K + B := by
    intro y hy
    have hk := hK y hy
    have hr := hraw y hy
    calc
      |j y| = |(X.drift * deriv w y + j y - q * w y) - (X.drift * deriv w y - q * w y)| := by congr 1; ring
      _ ≤ |X.drift * deriv w y + j y - q * w y| + |X.drift * deriv w y - q * w y| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (X.drift * deriv w y + j y - q * w y) (0 : ℝ) (X.drift * deriv w y - q * w y))
      _ ≤ K + B := add_le_add hk hr
  have hfbound : ∀ t, ‖f t‖ ≤ B := by
    intro t
    by_cases ht : t ∈ E
    · simp only [f, if_pos ht, Real.norm_eq_abs, abs_mul]
      calc
        |e t| * |X.drift * deriv w (Y t) - q * w (Y t)| ≤
          1 * |X.drift * deriv w (Y t) - q * w (Y t)| :=
            mul_le_mul_of_nonneg_right (he t) (abs_nonneg _)
        _ = |X.drift * deriv w (Y t) - q * w (Y t)| := one_mul _
        _ ≤ B := hraw (Y t) (hE t ht)
    · simp only [f, if_neg ht, norm_zero]
      dsimp [B]
      positivity
  have hgbound : ∀ t, ‖g t‖ ≤ K + B := by
    intro t
    by_cases ht : t ∈ E
    · simp only [g, if_pos ht, Real.norm_eq_abs, abs_mul]
      calc
        |e t| * |j (Y t)| ≤ 1 * |j (Y t)| :=
          mul_le_mul_of_nonneg_right (he t) (abs_nonneg _)
        _ = |j (Y t)| := one_mul _
        _ ≤ K + B := hgraw (Y t) (hE t ht)
    · simp only [g, if_neg ht, norm_zero]
      have hb : 0 ≤ B := by dsimp [B]; positivity
      linarith
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable B (Filter.Eventually.of_forall hfbound)
  have hgi : Integrable g μ := Integrable.of_bound hgm.aestronglyMeasurable (K + B) (Filter.Eventually.of_forall hgbound)
  have hpoint : ∀ t, (if t ∈ E then
      e t * (X.generator w (Y t) - q * w (Y t)) else 0) = f t + g t := by
    intro t
    by_cases ht : t ∈ E
    · simp only [if_pos ht, f, g]
      rw [boundedVariation_generator_physical_drift_representation
        X hBV w (Y t) (hGen (Y t) (hE t ht))]
      ring
    · simp only [if_neg ht, f, g, add_zero]
  have hint : (∫ t, if t ∈ E then
      e t * (X.generator w (Y t) - q * w (Y t)) else 0 ∂μ) =
        (∫ t, f t ∂μ) + ∫ t, g t ∂μ := by
    simp_rw [hpoint]
    exact integral_add hfi hgi
  change (∫ t, f t ∂μ) = -(∫ t, g t ∂μ) +
      (∫ t, if t ∈ E then
        e t * (X.generator w (Y t) - q * w (Y t)) else 0 ∂μ)
  rw [hint]
  ring
