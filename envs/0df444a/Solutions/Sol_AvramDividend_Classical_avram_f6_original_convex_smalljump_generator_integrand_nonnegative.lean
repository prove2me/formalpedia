-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_convex_smalljump_generator_integrand_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:37:06.776892+00:00
-- url     : https://prove2.me/submissions/0d5da092-98a1-4a01-b432-aa3038514dbe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_source_negative_mark_generator_exact_small_large_truncation_split
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hConvex : ConvexOn ℝ Set.univ w)
    (y z : ℝ) (hDiff : DifferentiableAt ℝ w y)
    (hz1 : -1 < z) (hz0 : z < 0) :
    0 ≤ SpectrallyNegativeLevy.generatorIntegrand w y z := by
  have hxy : y + z < y := by linarith
  have hslope := hConvex.slope_le_deriv
    (Set.mem_univ (y + z)) (Set.mem_univ y) hxy hDiff
  rw [slope_def_field] at hslope
  have hdenom : 0 < y - (y + z) := by linarith
  have htangent :
      w y - w (y + z) ≤ deriv w y * (y - (y + z)) :=
    (div_le_iff₀ hdenom).mp hslope
  have hk :=
    (avram_wave6_04_actual_source_negative_mark_generator_exact_small_large_truncation_split
      w y).1 z hz1 hz0
  rw [hk]
  nlinarith
