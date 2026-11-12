-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_original_gaussian_core_smallband_independence_centring
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:11:40.378843+00:00
-- url     : https://prove2.me/submissions/2460f7b1-78b2-4443-aa83-e865adbc415f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_intrinsic_gaussian_core_centered
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_smallband_cutoff_centered
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_intrinsic_gaussian_core_indep_smallband
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      ProbabilityTheory.IndepFun
        (fun ω =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
            avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω)
        (fun ω => -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) P ∧
      (∫ ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω ∂P) = 0 ∧
      (∫ ω,
        -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω ∂P) = 0 := by
  intro n t
  exact ⟨avram_ja21_original_intrinsic_gaussian_core_indep_smallband
      X hX hFinite n t,
    avram_ja21_original_intrinsic_gaussian_core_centered
      X hX hFinite t,
    avram_ja21_original_smallband_cutoff_centered
      X hX hFinite n t⟩
