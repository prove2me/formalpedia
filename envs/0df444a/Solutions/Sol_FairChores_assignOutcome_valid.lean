-- Prove2me | solution 1 for FairChores.assignOutcome_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:25:21.536051+00:00
-- url     : https://prove2.me/submissions/8ec8a0ec-5420-4ac2-8ed9-671784d32a4c

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution (p : T → ℝ) (assign : T → Option (Fin n)) (m : Fin n → ℝ)
    (hm0 : ∀ j, 0 ≤ m j) (hms : billOf p assign ≤ ∑ j, m j) :
    (assignOutcome assign m).Valid p := by
  classical
  refine ⟨?_, ?_, ?_, hm0, hms⟩
  · intro j
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [assignOutcome, Finset.mem_filter] at hx1 hx2
    rw [hx1.2] at hx2; exact absurd hx2.2 (by simp)
  · intro j k hjk
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [assignOutcome, Finset.mem_filter] at hx1 hx2
    rw [hx1.2] at hx2
    exact hjk (Option.some.inj hx2.2)
  · apply Finset.eq_univ_of_forall
    intro t
    simp only [assignOutcome, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    rcases h : assign t with _ | i
    · exact Or.inl rfl
    · exact Or.inr ⟨i, rfl⟩
end FairChores
