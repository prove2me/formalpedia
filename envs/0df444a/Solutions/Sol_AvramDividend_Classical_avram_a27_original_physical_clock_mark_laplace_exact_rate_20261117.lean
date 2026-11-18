-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_clock_mark_laplace_exact_rate_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:47:49.352403+00:00
-- url     : https://prove2.me/submissions/907c0357-c093-4c82-bcb5-4ecad12b21ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_normalised_negative_mark_laplace_and_rate_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_poisson_count_rate_real_clock_product_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original physical Poisson negative-mark moment has the exact horizon-scaled Levy rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (r : ℝ≥0)
    (hRate : (r : ℝ) =
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν) := by
  obtain ⟨m, hm0, hm1, hUnit⟩ :=
    avram_a27_original_normalised_negative_mark_laplace_and_rate_20261117
      X hFinite hNu θ hθ
  have hR : (r : ℝ) =
      (t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by
    rw [hRate]
    exact avram_a27_original_physical_poisson_count_rate_real_clock_product_20261117
      t (X.ν (Iio (0 : ℝ)))
  refine ⟨m, hm0, hm1, ?_⟩
  calc
    (r : ℝ) * (m - 1) =
        ((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) * (m - 1) := by
          rw [hR]
    _ = (t : ℝ) * ((X.ν (Iio (0 : ℝ))).toReal * (m - 1)) := by
          ring
    _ = _ := by rw [hUnit]
