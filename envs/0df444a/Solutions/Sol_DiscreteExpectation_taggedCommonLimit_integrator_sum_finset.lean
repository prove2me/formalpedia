-- Prove2me | solution 1 for DiscreteExpectation.taggedCommonLimit_integrator_sum_finset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:37:27.19535+00:00
-- url     : https://prove2.me/submissions/104530aa-6cd3-4e18-875f-5338435aafa1

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

theorem solution {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :
    TaggedCommonLimit a b (fun x => x) (fun x => ∑ i ∈ s, α i x)
      (∑ i ∈ s, rsIntegral (fun x => x) (α i) a b (h i)) := by -- `h i` works perfectly here
  induction' s using Finset.induction_on with i s' hi ih
  · simp only [Finset.sum_empty]
    exact sourceTaggedCommonLimit_zero_local a b hab
  · simp only [Finset.sum_insert hi]
    have H1 := rsIntegral_spec (h i)
    exact _root_.taggedCommonLimit_integrator_add H1 ih
