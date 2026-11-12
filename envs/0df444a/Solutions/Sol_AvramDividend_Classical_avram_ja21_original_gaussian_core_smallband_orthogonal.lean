-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja21_original_gaussian_core_smallband_orthogonal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:04:13.293525+00:00
-- url     : https://prove2.me/submissions/3c1ae43e-ab51-4cc3-8a1a-ea64e772302c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_independent_centered_real_components_orthogonal
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_smallband_independence_centring
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
      (∫ ω,
        (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) *
        (-avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ∂P) = 0 := by
  intro n t
  obtain ⟨hIndep, hGzero, hJzero⟩ :=
    avram_ja21_original_gaussian_core_smallband_independence_centring
      X hX hFinite n t
  obtain ⟨hGMeas, hJMeas⟩ :=
    avram_ja21_original_gaussian_core_and_jump_cutoff_measurable X n t
  exact avram_ja21_independent_centered_real_components_orthogonal P
    (fun ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω)
    (fun ω => -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
    hIndep
    ((hGMeas.mono (𝓕.le t) le_rfl).aestronglyMeasurable)
    ((hJMeas.mono (𝓕.le t) le_rfl).aestronglyMeasurable)
    hGzero hJzero
