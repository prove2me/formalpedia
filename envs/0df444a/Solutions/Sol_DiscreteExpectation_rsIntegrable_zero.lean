-- Prove2me | solution 1 for DiscreteExpectation.rsIntegrable_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:28:11.284877+00:00
-- url     : https://prove2.me/submissions/be4596de-838b-4828-a6f3-9f6b31772e9b

import Theorems.Thm_DiscreteExpectation_sourceHypotheses_zero_integrator
import Theorems.Thm_DiscreteExpectation_taggedCommonLimit_zero
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
    RSIntegrable (fun x => x) (fun _ => 0) a b := by
  -- 1. Construct the Darboux upper/lower common limit (evaluating to 0)
  have h_ul : UpperLowerCommonLimit a b (fun x => x) (fun x => 0) 0 := by
    refine ⟨sourceHypotheses_zero_integrator a b hab, ?_⟩
    intro eps heps
    -- Since the sum is exactly 0, any delta works. We arbitrarily pick 1.
    refine ⟨1, zero_lt_one, ?_⟩
    intro P _hmesh

    have h_up : upperSum P (fun x => x) (fun x => 0) = 0 := by
      unfold upperSum
      apply Finset.sum_eq_zero
      intro i _
      ring

    have h_low : lowerSum P (fun x => x) (fun x => 0) = 0 := by
      unfold lowerSum
      apply Finset.sum_eq_zero
      intro i _
      ring

    -- Substitute the sums and evaluate |0 - 0| < eps
    rw [h_up, h_low, sub_zero, abs_zero]
    exact ⟨heps, heps⟩

  -- 2. Fetch the Tagged limit (which we already proved evaluates to 0)
  have h_tg : TaggedCommonLimit a b (fun x => x) (fun x => 0) 0 :=
    taggedCommonLimit_zero a b hab

  -- 3. Package them into the `RSIntegralWitness` structure.
  -- The existential `Nonempty` wrapper is satisfied by `⟨...⟩`
  exact ⟨⟨0, h_ul, h_tg⟩⟩
end DiscreteExpectation
end DiscreteExpectation
