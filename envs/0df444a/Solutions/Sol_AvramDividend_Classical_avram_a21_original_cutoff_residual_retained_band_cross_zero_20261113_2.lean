-- Prove2me | solution 2 for AvramDividend.Classical.avram_a21_original_cutoff_residual_retained_band_cross_zero_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:12:43.467271+00:00
-- url     : https://prove2.me/submissions/d824debe-3d63-44aa-ab2c-12bbc82c4140
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_retained_cross_zero_base_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_positive_cutoff_residual_retained_band_cross_zero_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every physical retained-band residual covariance is zero by the zero index and positive-index cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      let Rn : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
      let Jn : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
      Integrable (fun ω => Rn ω * Jn ω) P ∧
        (∫ ω, Rn ω * Jn ω ∂P) = 0 := by
  intro n t
  cases n with
  | zero =>
      exact avram_a21_original_zero_retained_cross_zero_base_20261113 X t
  | succ k =>
      simpa only [Nat.succ_eq_add_one] using
        (avram_a21_original_positive_cutoff_residual_retained_band_cross_zero_20261113
          X hX hFinite k t)
