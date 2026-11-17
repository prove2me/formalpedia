-- Prove2me | solution 1 for DiscreteExpectation.step_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:56:17.805931+00:00
-- url     : https://prove2.me/submissions/f69f577f-bfe9-4cb9-8fc4-2da2dd3407c3

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

theorem solution {c : ℝ} : Monotone (stepIndicator c) := by
  intro x y hxy
  unfold stepIndicator
  split_ifs with h1 h2
  · rfl
  · exfalso; linarith
  · exact zero_le_one
  · rfl
end DiscreteExpectation
end DiscreteExpectation
