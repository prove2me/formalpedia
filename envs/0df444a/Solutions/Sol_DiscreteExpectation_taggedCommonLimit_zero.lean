-- Prove2me | solution 1 for DiscreteExpectation.taggedCommonLimit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:05:17.448188+00:00
-- url     : https://prove2.me/submissions/61f90285-990a-4b2e-91e9-5432ad12e3ad

import Theorems.Thm_DiscreteExpectation_sourceHypotheses_zero_integrator
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
end
noncomputable section DiscreteExpectation
section DiscreteExpectation
open DiscreteExpectation

theorem solution (a b : ℝ) (hab : a < b) :
    TaggedCommonLimit a b (fun x => x) (fun _ => 0) 0 := by
  refine ⟨sourceHypotheses_zero_integrator a b hab, ?_⟩
  intro eps heps
  refine ⟨1, zero_lt_one, ?_⟩
  intro P tags htags hmesh
  have hS : taggedSum P tags (fun x => x) (fun x => 0) = 0 := by
    unfold taggedSum; apply Finset.sum_eq_zero; intro i _; ring
  rw [hS, sub_zero, abs_zero]
  exact heps
end DiscreteExpectation
end DiscreteExpectation
