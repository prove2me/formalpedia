-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_source_generator_interior_C2_taylor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:30:28.159863+00:00
-- url     : https://prove2.me/submissions/dd746841-2264-497d-99f9-e012aea3f5d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_positive_C2_backward_taylor_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set MeasureTheory

/-- The genuine source Lévy generator compensator is the triangular C² kernel. -/
theorem solution
    (W : ℝ → ℝ) (hW : ContDiffOn ℝ 2 W (Ioi 0))
    (x y : ℝ) (hy1 : -1 < y) (hy0 : y < 0) (hx : 0 < x + y) :
    SpectrallyNegativeLevy.generatorIntegrand W x y =
      ∫ t in (x + y)..x, (t - (x + y)) * iteratedDeriv 2 W t := by
  have hlt : x + y < x := by linarith
  have hTaylor := avram_wave3_05_positive_C2_backward_taylor_exact W hW
    (x + y) x hx hlt
  have hy : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy1, by linarith⟩
  have hi : (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 1 := by
    simp [Set.indicator_of_mem hy]
  unfold SpectrallyNegativeLevy.generatorIntegrand
  rw [hi]
  convert hTaylor using 1 <;> ring
