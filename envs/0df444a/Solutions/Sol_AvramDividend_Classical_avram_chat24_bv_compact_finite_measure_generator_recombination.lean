-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_bv_compact_finite_measure_generator_recombination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:49:57.774879+00:00
-- url     : https://prove2.me/submissions/cd213cc6-7c70-4239-87c0-b1c7bdb2c534

import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_negative_jump_generator_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_shift_compact_kernel_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_result_001_avram_dividend_classical_avram_chat24_bv_compact_integrability_09b2e7a8
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (w : ℝ → ℝ) (hwm : Measurable w)
    (q a b L R A : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
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
  classical
  let J : ℝ → ℝ := fun y => ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν
  let F : ι → ℝ := fun t => if t ∈ E then
    e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0
  let G : ι → ℝ := fun t => if t ∈ E then
    e t * (X.drift * deriv w (Y t) + J (Y t) - q * w (Y t)) else 0
  have hJm : Measurable J := avram_p3_e_compensator_original_negative_jump_generator_measurable
    X (avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite X) w hwm
  have hFm : Measurable F :=
    Measurable.ite hEm (hem.mul ((measurable_const.mul ((measurable_deriv w).comp hYm)).sub
      (measurable_const.mul (hwm.comp hYm)))) measurable_const
  have hGm : Measurable G :=
    Measurable.ite hEm (hem.mul (((measurable_const.mul ((measurable_deriv w).comp hYm)).add
      (hJm.comp hYm)).sub (measurable_const.mul (hwm.comp hYm)))) measurable_const
  obtain ⟨K, hK, hKb⟩ := avram_p3_e_compensator_original_BV_compact_HJB_drift_uniform
    X hBV w hwm q a b L R A ha ha2 hab hL hR hA hLip hW hDeriv
  have hF : Integrable F μ := result_001_avram_dividend_classical_avram_chat24_bv_compact_integrability_09b2e7a8 (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (X := X) (hBV := hBV) (w := w) (hwm := hwm) (q := q) (a := a) (b := b) (L := L) (R := R) (A := A) (ha := ha) (ha2 := ha2) (hab := hab) (hL := hL) (hR := hR) (hA := hA) (hLip := hLip) (hW := hW) (hDeriv := hDeriv) (hGen := hGen) (ι := ι) (μ := μ) (Y := Y) (e := e) (hYm := hYm) (hem := hem) (he := he) (E := E) (hEm := hEm) (hE := hE) (hJm := hJm) (hFm := hFm) (hGm := hGm)
  have hG : Integrable G μ := (integrable_const K).mono' hGm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      by_cases ht : t ∈ E
      · simp only [G, if_pos ht]
        change ‖e t * (X.drift * deriv w (Y t) + J (Y t) - q * w (Y t))‖ ≤ K
        rw [Real.norm_eq_abs, abs_mul]
        simpa using mul_le_mul (he t) (hKb _ (hE t ht)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      · simpa [G, ht] using hK)
  have hcomp : (fun t => if t ∈ E then e t * J (Y t) else 0) = G - F := by
    funext t
    dsimp [G, F]
    split_ifs <;> ring
  have hgen : (fun t => if t ∈ E then e t * (X.generator w (Y t) - q * w (Y t)) else 0) = G := by
    funext t
    by_cases ht : t ∈ E
    · simp only [G, if_pos ht,
        boundedVariation_generator_physical_drift_representation X hBV w (Y t) (hGen _ (hE t ht)), J]
    · simp [G, ht]
  change (∫ t, F t ∂μ) = -(∫ t, if t ∈ E then e t * J (Y t) else 0 ∂μ) + _
  rw [hcomp, hgen]
  change (∫ t, F t ∂μ) = -(∫ t, G t - F t ∂μ) + (∫ t, G t ∂μ)
  rw [integral_sub hG hF]
  ring
end
