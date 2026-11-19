-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_uniform_compound_Standing_counterexample_nearzero_variance_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:14:07.799375+00:00
-- url     : https://prove2.me/submissions/70eb3a83-9ac0-49f9-92e9-354f36c288aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_nearzero_variance_formula_forces_zero_band_energy
import Theorems.Thm_AvramDividend_Classical_avram_ja18_uniform_negative_smallmark_quadratic_energy_one_third
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Genuine original finite-activity Standing source refutes the incorrect complementary-band formula. -/
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.ν (Iio (0 : ℝ)) ≠ ⊤ ∧
      ¬ (∀ (n : ℕ) (t : ℝ≥0),
        (∫ ω,
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2 ∂P) =
          (t : ℝ) *
            (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) := by
  obtain ⟨P, 𝓕, X, hX, hBV, hν, hFin, hDrift, hσ⟩ :=
    avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists
  refine ⟨P, 𝓕, X, hX, ne_of_lt hFin, ?_⟩
  intro hNear
  have hZero :=
    avram_ja18_original_nearzero_variance_formula_forces_zero_band_energy
      X hX (ne_of_lt hFin) hNear
  rw [hν, avram_ja18_uniform_negative_smallmark_quadratic_energy_one_third] at hZero
  norm_num at hZero
