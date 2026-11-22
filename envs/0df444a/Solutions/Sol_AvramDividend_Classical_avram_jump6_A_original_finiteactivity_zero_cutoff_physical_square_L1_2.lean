-- Prove2me | solution 2 for AvramDividend.Classical.avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:42:03.635516+00:00
-- url     : https://prove2.me/submissions/418d243e-bc99-4b87-a8b2-c54996e1e661
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_ja18i_original_zero_cutoff_gaussian_square_integrable
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 T ω) ^ 2) P  := by
  exact avram_ja18i_original_zero_cutoff_gaussian_square_integrable X hX hFinite T
