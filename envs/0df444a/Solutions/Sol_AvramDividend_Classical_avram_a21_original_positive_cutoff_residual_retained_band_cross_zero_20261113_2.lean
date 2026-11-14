-- Prove2me | solution 2 for AvramDividend.Classical.avram_a21_original_positive_cutoff_residual_retained_band_cross_zero_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:33:14.547417+00:00
-- url     : https://prove2.me/submissions/409127f2-1af0-4e56-a5eb-19ac0f1f8e42
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_every_cutoff_residual_integrable_centered_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_positive_time_disjoint_cutoff_residual_retained_independence_L1_20261113
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Orthogonality of the physical cutoff residual to the retained negative mark band from positive-time independence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      let R : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω
      Integrable (fun ω => R ω * J ω) P ∧
        (∫ ω, R ω * J ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro n t
  let R : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω
  change Integrable (fun ω => R ω * J ω) P ∧
    (∫ ω, R ω * J ω ∂P) = 0
  by_cases ht : t = 0
  · subst t
    have hJ0 : ∀ ω : Ω, J ω = 0 := by
      intro ω
      exact avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_time
        X (n + 1) ω
    simp [hJ0]
  · have htpos : 0 < t := lt_of_le_of_ne zero_le (Ne.symm ht)
    obtain ⟨hInd, hJ⟩ :=
      avram_a21_positive_time_disjoint_cutoff_residual_retained_independence_L1_20261113
        X hX hFinite n t htpos
    obtain ⟨hR, hMeanR⟩ :=
      avram_a21_original_every_cutoff_residual_integrable_centered_20261113
        X hX hFinite (n + 1) t
    refine ⟨hInd.integrable_mul hR hJ, ?_⟩
    calc
      (∫ ω, R ω * J ω ∂P) =
          (∫ ω, R ω ∂P) * (∫ ω, J ω ∂P) :=
            hInd.integral_mul_eq_mul_integral hR.aestronglyMeasurable hJ.aestronglyMeasurable
      _ = 0 := by rw [hMeanR, zero_mul]
