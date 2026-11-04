-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_negative_mark_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:59:11.823092+00:00
-- url     : https://prove2.me/submissions/45337f42-dd22-43ea-b211-9cb305c4dfa0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine X.ν small-negative linear mark energy, with predictable original
source coefficient and a finite physical predictable clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (M : ℝ) (hM : 0 ≤ M) (hg : ∀ p, |g p| ≤ M) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => g p.1 * p.2) ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) < ⊤) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  change Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => g p.1 * p.2) ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) < ⊤
  constructor
  · exact (hgm.comp measurable_fst).mul measurable_snd
  · let S : ℝ≥0∞ :=
      ∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal (z ^ 2) ∂X.ν
    have hS : S < ⊤ :=
      finite_small_negative_jump_square_moment X.ν X.ν_integrable
    have hmeas : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ 2)) := by
      fun_prop
    have hpoint (p : ℝ≥0 × Ω) (z : ℝ) :
        (g p * z)^2 ≤ M^2 * z^2 := by
      have hsq : (g p)^2 ≤ M^2 :=
        sq_le_sq.mpr (by simpa [abs_of_nonneg hM] using hg p)
      calc
        (g p * z)^2 = (g p)^2 * z^2 := by ring
        _ ≤ M^2 * z^2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg z)
    have hinner (p : ℝ≥0 × Ω) :
        (∫⁻ z in Ioo (-1 : ℝ) 0,
          ENNReal.ofReal ((g p * z)^2) ∂X.ν) ≤
          ENNReal.ofReal (M^2) * S := by
      calc
        (∫⁻ z in Ioo (-1 : ℝ) 0,
          ENNReal.ofReal ((g p * z)^2) ∂X.ν) ≤
          ∫⁻ z in Ioo (-1 : ℝ) 0,
            ENNReal.ofReal (M^2) * ENNReal.ofReal (z^2) ∂X.ν := by
              apply setLIntegral_mono (by fun_prop)
              intro z hz
              rw [← ENNReal.ofReal_mul (sq_nonneg M)]
              exact ENNReal.ofReal_le_ofReal (hpoint p z)
        _ = _ := lintegral_const_mul _ hmeas
    calc
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) ≤
          ∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal (M^2) * S ∂μ :=
            lintegral_mono hinner
      _ = μ Set.univ * (ENNReal.ofReal (M^2) * S) := by simp [mul_comm]
      _ < ⊤ := ENNReal.mul_lt_top hμ
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS)