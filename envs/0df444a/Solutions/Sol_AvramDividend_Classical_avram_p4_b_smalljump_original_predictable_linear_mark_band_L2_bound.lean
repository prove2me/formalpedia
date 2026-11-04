-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_mark_band_L2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:04:51.513621+00:00
-- url     : https://prove2.me/submissions/7658fce5-b72d-40f7-8229-99c58b956f09

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A quantitative actual-source L2 bound on arbitrary negative-mark bands.
The expected jump-count/isometry statement remains a separate obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (M : ℝ) (hM : 0 ≤ M) (hg : ∀ p, |g p| ≤ M)
    (B : Set ℝ)
    (hBmom : (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν) < ⊤) :
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) ≤ μ Set.univ * (ENNReal.ofReal (M^2) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν)) ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) < ⊤ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hpoint (p : ℝ≥0 × Ω) (z : ℝ) :
      (g p * z)^2 ≤ M^2 * z^2 := by
    have hsq : (g p)^2 ≤ M^2 :=
      sq_le_sq.mpr (by simpa [abs_of_nonneg hM] using hg p)
    calc
      (g p * z)^2 = (g p)^2 * z^2 := by ring
      _ ≤ M^2 * z^2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg z)
  have hinner (p : ℝ≥0 × Ω) :
      (∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν) ≤
        ENNReal.ofReal (M^2) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν) := by
    calc
      (∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν) ≤
          ∫⁻ z in B, ENNReal.ofReal (M^2) * ENNReal.ofReal (z^2) ∂X.ν := by
            apply setLIntegral_mono (by fun_prop)
            intro z hz
            rw [← ENNReal.ofReal_mul (sq_nonneg M)]
            exact ENNReal.ofReal_le_ofReal (hpoint p z)
      _ = _ := lintegral_const_mul _ (by fun_prop)
  have hbound : (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) ≤
      μ Set.univ * (ENNReal.ofReal (M^2) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν)) := by
    calc
      (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) ≤
          ∫⁻ p : ℝ≥0 × Ω,
            ENNReal.ofReal (M^2) * (∫⁻ z in B, ENNReal.ofReal (z^2) ∂X.ν) ∂μ :=
              lintegral_mono hinner
      _ = _ := by simp [mul_comm]
  exact ⟨hbound, lt_of_le_of_lt hbound
    (ENNReal.mul_lt_top hμ
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBmom))⟩
