-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn11_levy_real_mark_loss_conversion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:56:48.016231+00:00
-- url     : https://prove2.me/submissions/7f231cdd-c1d1-4014-8354-86141ca9e77c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Convert the finite original Lévy cutoff loss from ENNReal to its
Bochner form using finite band mass and bounded nonnegative marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
    let B : Set ℝ := Iio (-ε)
    (((T : ℝ≥0∞) * (∫⁻ y in B, φ y ∂X.ν))).toReal =
      (1 / ((n : ℝ) + 1)) *
        (∫ y in B, (1 - Real.exp y) ∂X.ν) := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let ε : ℝ := 1 / ((k : ℝ) + 1)
  let B : Set ℝ := Iio (-ε)
  let f : ℝ → ℝ := fun y => 1 - Real.exp y
  let μ : Measure ℝ := X.ν.restrict B
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hBfin : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite
      X B (by simpa only [B] using measurableSet_Iio) ε hε
        (by intro y hy; change y < -ε at hy; exact le_of_lt hy)
  letI : IsFiniteMeasure μ := ⟨by simpa [μ, B] using hBfin⟩
  have hmeas : Measurable f := by dsimp [f]; fun_prop
  have hnonneg : ∀ᵐ y ∂μ, 0 ≤ f y := by
    filter_upwards [ae_restrict_mem (by simpa only [B] using measurableSet_Iio)]
      with y hy
    have hyneg : y ≤ 0 := by
      have hn : -ε ≤ 0 := by linarith [hε]
      have hyl : y < -ε := by simpa only [B, Set.mem_Iio] using hy
      exact le_trans (le_of_lt hyl) hn
    have hexp : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hyneg
    dsimp [f]
    linarith
  have hbd : ∀ᵐ y ∂μ, ‖f y‖ ≤ (1 : ℝ) := by
    filter_upwards [hnonneg] with y hy
    have hp : 0 ≤ Real.exp y := le_of_lt (Real.exp_pos y)
    rw [Real.norm_eq_abs, abs_of_nonneg hy]
    dsimp [f]
    linarith
  have hint : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable hbd
  have hreal : (∫ y, f y ∂μ) =
      (∫⁻ y, ENNReal.ofReal (f y) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable
  have hconv : ((∫⁻ y in B, ENNReal.ofReal (f y) ∂X.ν)).toReal =
      (∫ y in B, f y ∂X.ν) := by
    simpa only [μ] using hreal.symm
  dsimp only [T, ε, B, f]
  rw [ENNReal.toReal_mul]
  rw [hconv]
  congr 1
  all_goals simp [T]
