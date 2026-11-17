-- Prove2me | solution 1 for DiscreteExpectation.sourceHyp_id_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:05:09.538018+00:00
-- url     : https://prove2.me/submissions/346cafc7-eed4-4125-b9fb-43334c65b9c2

import Theorems.Thm_DiscreteExpectation_step_mono
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

theorem solution (c a b : ℝ) (ha : a < c) (hb : c < b) :
    SourceHypotheses a b (fun x => x) (stepIndicator c) := by
  refine ⟨by linarith, ?_, ?_, step_mono.monotoneOn _⟩
  · exact ⟨b, by rintro y ⟨x, hx, rfl⟩; exact hx.2⟩
  · exact ⟨a, by rintro y ⟨x, hx, rfl⟩; exact hx.1⟩
end DiscreteExpectation
end DiscreteExpectation
