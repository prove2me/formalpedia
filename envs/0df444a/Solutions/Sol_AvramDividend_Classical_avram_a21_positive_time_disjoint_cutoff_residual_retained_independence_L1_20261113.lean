-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_positive_time_disjoint_cutoff_residual_retained_independence_L1_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:24:54.647413+00:00
-- url     : https://prove2.me/submissions/7690fe77-9a66-4f68-ab3b-e783b6fe4696
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_positive_cutoff_residual_retained_independence_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_retained_compensated_negative_band_L1_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Independence plus proved source L1 supplies the full disjoint-noise certificate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      let R : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω
      ProbabilityTheory.IndepFun R J P ∧ Integrable J P := by
  intro n t ht
  exact ⟨
    avram_a21_original_positive_cutoff_residual_retained_independence_20261113
      X hX hFinite n t ht,
    avram_a21_original_retained_compensated_negative_band_L1_20261113
      X hFinite (n + 1) t⟩
