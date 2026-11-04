-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_discounted_physical_generator_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:20:33.351963+00:00
-- url     : https://prove2.me/submissions/b8549c59-ecee-43cf-8569-dfd6490b0e09

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- An explicit uniform physical drift, original negative-jump and discount envelope on every finite nonnegative clock. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (t : ℝ≥0) (y : ℝ)
  (L M R : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M) (hR : 0 ≤ R)
  (hDeriv : |deriv w y| ≤ L)
  (hJump : |∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν| ≤ M)
  (hValue : |w y| ≤ R) :
  0 ≤ |X.drift| * L + M + |q| * R ∧
  |Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y)| ≤ |X.drift| * L + M + |q| * R := by
  let J : ℝ := ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν
  have hDrift : |X.drift * deriv w y| ≤ |X.drift| * L := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hDeriv (abs_nonneg _)
  have hDisc : |q * w y| ≤ |q| * R := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hValue (abs_nonneg _)
  have hTriangle :
      |X.drift * deriv w y + J - q * w y| ≤
      |X.drift * deriv w y| + |J| + |q * w y| := by
    calc
      _ ≤ |X.drift * deriv w y + J| + |q * w y| := abs_sub _ _
      _ ≤ (|X.drift * deriv w y| + |J|) + |q * w y| := by
        have hadd : |X.drift * deriv w y + J| ≤
            |X.drift * deriv w y| + |J| := abs_add_le _ _
        linarith
  have hBase :
      |X.drift * deriv w y + J - q * w y| ≤
      |X.drift| * L + M + |q| * R := by
    have hJump' : |J| ≤ M := hJump
    linarith
  have hExp : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
    nlinarith [mul_nonneg hq ht]
  constructor
  · positivity
  · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-(q * (t : ℝ))) *
          |X.drift * deriv w y + J - q * w y| ≤
          1 * |X.drift * deriv w y + J - q * w y| :=
        mul_le_mul_of_nonneg_right hExp (abs_nonneg _)
      _ = |X.drift * deriv w y + J - q * w y| := one_mul _
      _ ≤ |X.drift| * L + M + |q| * R := hBase
