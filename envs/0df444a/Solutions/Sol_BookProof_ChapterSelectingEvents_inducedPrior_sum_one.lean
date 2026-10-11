-- Prove2me | solution 1 for BookProof.ChapterSelectingEvents.inducedPrior_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:30:56.321552+00:00
-- url     : https://prove2.me/submissions/d4d67f7b-43cb-4393-8e2d-16ddb327c60e

-- Generated from ChapterSelectingEvents.lean — solution of BookProof.ChapterSelectingEvents.inducedPrior_sum_one
import Mathlib
import Definitions.Def_ChapterSelectingEvents
import Definitions.Def_ChapterDeepLearningSampling
open BookProof.ChapterSelectingEvents



open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω Data : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {Seed Model : Type*} [Fintype Seed] [Fintype Model] [DecidableEq Model]

set_option maxHeartbeats 1000000 in
theorem solution (seedProb : Seed → ℝ) (train : Seed → Model)
    (_hnonneg : ∀ s, 0 ≤ seedProb s) (hsum : ∑ s, seedProb s = 1) :
    ∑ m, inducedPrior seedProb train m = 1 := by

  unfold inducedPrior
  -- The sum over all models of the fiber sum equals the total sum over seeds
  classical
    calc
      ∑ m, ∑ s ∈ Finset.filter (fun s => train s = m) Finset.univ, seedProb s
          = ∑ s, seedProb s := by
        rw [Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ train seedProb]
        simp
      _ = 1 := hsum
