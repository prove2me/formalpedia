-- Prove2me | solution 3 for AvramDividend.Classical.avram_ja18i_original_zero_cutoff_gaussian_square_integrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:22:05.101551+00:00
-- url     : https://prove2.me/submissions/45536ac3-e6c3-4399-be7a-cff66c293ad2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_cutoff_gaussian_plus_all_smallmarks_second_moment_20261113_v2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original zero-cutoff square integrability from its exact physical moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (t : ℝ≥0), Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) P := by
  intro t
  exact (avram_a21_original_zero_cutoff_gaussian_plus_all_smallmarks_second_moment_20261113_v2
    X hX hFinite t).1
