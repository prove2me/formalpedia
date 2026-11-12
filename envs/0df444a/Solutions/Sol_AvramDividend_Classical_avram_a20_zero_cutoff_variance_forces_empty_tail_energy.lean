-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_zero_cutoff_variance_forces_empty_tail_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:58:41.322552+00:00
-- url     : https://prove2.me/submissions/d54eea96-8ad0-4665-81db-1d27cf2740ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Cutoff-zero variance cannot equal the omitted negative-unit tail unless its energy vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hVar : ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) :
    (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂X.ν) = 0 := by
  have hh := hVar 0 1
  simp [avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff] at hh
  norm_num at hh
  exact hh.symm
