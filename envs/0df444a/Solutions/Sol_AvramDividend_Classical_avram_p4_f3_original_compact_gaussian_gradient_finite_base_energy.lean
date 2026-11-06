-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_compact_gaussian_gradient_finite_base_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:48:47.120647+00:00
-- url     : https://prove2.me/submissions/1916cc25-8d77-4712-8a33-b91c4a082671

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian gradient coefficient has finite quadratic energy on each strictly interior finite-mass localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    {S : Type*} [mS : MeasurableSpace S]
    (μ : Measure S) (hμ : μ Set.univ < ⊤)
    (U : S → ℝ) (hU : ∀ s, U s ∈ Icc δ K) :
    (∫⁻ s, ENNReal.ofReal ((X.σ * deriv w (U s)) ^ 2) ∂μ) < ⊤ := by
  have hC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  obtain ⟨A, hA0, hA⟩ :=
    avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
      C w δ K hδ hδK hK hC1
  let B : ℝ := |X.σ| * A
  have hB0 : 0 ≤ B := mul_nonneg (abs_nonneg _) hA0
  have hCoeff (s : S) : |X.σ * deriv w (U s)| ≤ B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hA (U s) (hU s)) (abs_nonneg _)
  have hSquare (s : S) : (X.σ * deriv w (U s)) ^ 2 ≤ B ^ 2 := by
    have hsub : 0 ≤ B - |X.σ * deriv w (U s)| :=
      sub_nonneg.mpr (hCoeff s)
    have hadd : 0 ≤ B + |X.σ * deriv w (U s)| :=
      add_nonneg hB0 (abs_nonneg _)
    nlinarith [mul_nonneg hsub hadd, sq_abs (X.σ * deriv w (U s))]
  have hPoint (s : S) :
      ENNReal.ofReal ((X.σ * deriv w (U s)) ^ 2) ≤
        ENNReal.ofReal (B ^ 2) :=
    ENNReal.ofReal_le_ofReal (hSquare s)
  calc
    (∫⁻ s, ENNReal.ofReal ((X.σ * deriv w (U s)) ^ 2) ∂μ)
      ≤ ∫⁻ _s : S, ENNReal.ofReal (B ^ 2) ∂μ :=
        lintegral_mono hPoint
    _ = ENNReal.ofReal (B ^ 2) * μ Set.univ := by
      simp [MeasureTheory.lintegral_const, mul_comm]
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hμ
