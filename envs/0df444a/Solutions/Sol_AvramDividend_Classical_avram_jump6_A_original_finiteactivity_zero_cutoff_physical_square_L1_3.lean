-- Prove2me | solution 3 for AvramDividend.Classical.avram_jump6_A_original_finiteactivity_zero_cutoff_physical_square_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:24:33.932172+00:00
-- url     : https://prove2.me/submissions/f6a50af0-bb01-41cd-a83d-ec6909fac27f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finiteactivity_zero_sigma_cutoff_physical_square_L1
import Theorems.Thm_AvramDividend_Classical_avram_ja18i_original_zero_cutoff_gaussian_square_integrable
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
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
  by_cases hSigma : X.σ = 0
  · exact avram_jump6_A_original_finiteactivity_zero_sigma_cutoff_physical_square_L1
      X hX hFinite hSigma T
  · exact avram_ja18i_original_zero_cutoff_gaussian_square_integrable
      X hX hFinite T
