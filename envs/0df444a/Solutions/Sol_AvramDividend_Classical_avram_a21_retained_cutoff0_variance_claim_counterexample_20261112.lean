-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_retained_cutoff0_variance_claim_counterexample_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:22:12.169934+00:00
-- url     : https://prove2.me/submissions/72cd4d51-16c9-4197-89fa-2d9cd02b7541

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a20_negative_uniform_original_standing_source_exists
import Theorems.Thm_AvramDividend_Classical_avram_a20_uniform_negative_levy_square_mass_positive
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Counterexample to the claimed omitted-tail variance at cutoff zero:
the physical retained jump band is empty, yet a standing finite-activity
Lévy source has strictly positive squared-mark mass on (-1,0). -/
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.ν (Iio (0 : ℝ)) ≠ ⊤ ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_small_band_compensated
        X 0 (1 : ℝ≥0) ω) ^ 2 ∂P) ≠
        (1 : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂X.ν) := by
  rcases avram_a20_negative_uniform_original_standing_source_exists with
    ⟨P, 𝓕, X, hStanding, hNu, hFinite⟩
  refine ⟨P, 𝓕, X, hStanding, ne_of_lt hFinite, ?_⟩
  have hPos : 0 < (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂X.ν) := by
    rw [hNu]
    exact avram_a20_uniform_negative_levy_square_mass_positive
  have hZero :
      (∫ ω, (avram_p4_h_gaussian_intrinsic_small_band_compensated
        X 0 (1 : ℝ≥0) ω) ^ 2 ∂P) = 0 := by
    simp [avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff]
  rw [hZero, one_mul]
  exact ne_of_lt hPos
