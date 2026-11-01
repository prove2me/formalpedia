-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:36:54.71047+00:00
-- url     : https://prove2.me/submissions/7fb1df1a-4ef8-4740-8677-06d29c3127b2

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exact original-source compensated Lévy kernel is a large-jump-only
difference at reserves one full jump unit above the barrier, including ruin crossing. -/
theorem solution
    (W : ℝ → ℝ) (x y : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x) (hy : y < 0) :
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y =
      if y ≤ -1 then vcstar W (x + y) - vcstar W x else 0 := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hx : a < x := by dsimp [a] at *; linarith
  by_cases hlarge : y ≤ -1
  · have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
      intro hmem
      exact (not_lt_of_ge hlarge) hmem.1
    simp only [if_pos hlarge]
    unfold SpectrallyNegativeLevy.generatorIntegrand
    simp [Set.indicator_of_notMem hnot]
  · have hy1 : -1 < y := lt_of_not_ge hlarge
    have hxy : a < x + y := by dsimp [a] at *; linarith
    have hz :
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y = 0 := by
      change SpectrallyNegativeLevy.generatorIntegrand
        (barrierValue W a) x y = 0
      exact barrier_generatorIntegrand_zero_small_negative_jump_above
        W a x y ha hx hxy hy1 hy
    simpa [hlarge] using hz
