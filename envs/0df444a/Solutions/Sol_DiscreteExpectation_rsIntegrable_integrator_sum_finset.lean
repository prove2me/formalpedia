-- Prove2me | solution 1 for DiscreteExpectation.rsIntegrable_integrator_sum_finset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:37:19.029277+00:00
-- url     : https://prove2.me/submissions/d4b2ee33-8f1c-4e75-844c-8ecbfd37c1e3

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Tactic
import Theorems.Thm_taggedCommonLimit_integrator_add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DiscreteExpectation
open scoped BigOperators Pointwise
noncomputable section

private lemma sourceHypotheses_zero_integrator_local (a b : ℝ) (hab : a < b) :
    SourceHypotheses a b (fun x => x) (fun _ => 0) := by
  refine ⟨hab, ?_, ?_, ?_⟩
  · exact ⟨b, by rintro y ⟨x, hx, rfl⟩; exact hx.2⟩
  · exact ⟨a, by rintro y ⟨x, hx, rfl⟩; exact hx.1⟩
  · intro x hx y hy hxy; rfl

private theorem sourceTaggedCommonLimit_zero_local (a b : ℝ) (hab : a < b) :
    TaggedCommonLimit a b (fun x => x) (fun _ => 0) 0 := by
  refine ⟨sourceHypotheses_zero_integrator_local a b hab, ?_⟩
  intro eps heps
  refine ⟨1, zero_lt_one, ?_⟩
  intro P tags htags hmesh
  have hS : taggedSum P tags (fun x => x) (fun x => 0) = 0 := by
    unfold taggedSum; apply Finset.sum_eq_zero; intro i _; ring
  rw [hS, sub_zero, abs_zero]
  exact heps

private theorem sourceRSIntegrable_zero_local (a b : ℝ) (hab : a < b) :
    RSIntegrable (fun x => x) (fun _ => 0) a b := by
  -- 1. Construct the Darboux upper/lower common limit (evaluating to 0)
  have h_ul : UpperLowerCommonLimit a b (fun x => x) (fun x => 0) 0 := by
    refine ⟨sourceHypotheses_zero_integrator_local a b hab, ?_⟩
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
    sourceTaggedCommonLimit_zero_local a b hab

  -- 3. Package them into the `RSIntegralWitness` structure.
  -- The existential `Nonempty` wrapper is satisfied by `⟨...⟩`
  exact ⟨⟨0, h_ul, h_tg⟩⟩

theorem solution {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :  
    RSIntegrable (fun x => x) (fun x => ∑ i ∈ s, α i x) a b := by
  induction' s using Finset.induction_on with i s' hi ih
  · simp only [Finset.sum_empty]
    exact sourceRSIntegrable_zero_local a b hab
  · simp only [Finset.sum_insert hi]
    -- Now we just pass `h i` directly!
    exact rsIntegrable_integrator_add (h i) ih
