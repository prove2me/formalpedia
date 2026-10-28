-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrand_negative_jump_reflection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:35:38.814508+00:00
-- url     : https://prove2.me/submissions/245db9ba-1aff-4cc0-b6a5-9bb68d6da1c0

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- The signed-jump generator kernel matches the positive-magnitude kernel under negation. -/
theorem solution
    (W : ℝ → ℝ) (x y : ℝ) (hy : y < 0) :
    W (x - (-y)) - W x +
      (if -y < 1 then (-y) * deriv W x else 0) =
    SpectrallyNegativeLevy.generatorIntegrand W x y := by
  unfold SpectrallyNegativeLevy.generatorIntegrand
  rw [sub_neg_eq_add]
  by_cases hsmall : -1 < y
  · have hI : y ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
    have hif : -y < 1 := by linarith
    simp only [if_pos hif, Set.indicator_of_mem hI, Pi.one_apply]
    ring
  · have hI : y ∉ Ioo (-1 : ℝ) 1 := by
      intro h
      exact hsmall h.1
    have hif : ¬(-y < 1) := by linarith
    simp only [if_neg hif, Set.indicator_of_notMem hI]
    ring
