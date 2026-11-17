-- Prove2me | solution 1 for DiscreteExpectation.sourceHypotheses_zero_integrator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:55:38.979974+00:00
-- url     : https://prove2.me/submissions/633e3736-f70f-474b-8edd-ce3ff274c937

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
    SourceHypotheses a b (fun x => x) (fun _ => 0) := by
  refine ⟨hab, ?_, ?_, ?_⟩
  · exact ⟨b, by rintro y ⟨x, hx, rfl⟩; exact hx.2⟩
  · exact ⟨a, by rintro y ⟨x, hx, rfl⟩; exact hx.1⟩
  · intro x hx y hy hxy; rfl
end DiscreteExpectation
end DiscreteExpectation
