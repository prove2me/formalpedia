-- Prove2me | solution 1 for Falmagne.upperSum_rankingEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:35.027828+00:00
-- url     : https://prove2.me/submissions/93c03573-56ac-47a0-88d0-c189200c7548

module
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
public import Theorems.Thm_Falmagne_mem_lowerContour
public import Theorems.Thm_Falmagne_rankingEdge_eq_zero_of_not_mem
public import Theorems.Thm_Falmagne_self_mem_lowerContour
attribute [local simp] Falmagne.mem_lowerContour
attribute [local simp] Falmagne.rankingEdge_eq_zero_of_not_mem



set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
namespace Falmagne
theorem _root_.solution (hl : IsRanking l) (x : X) (A : Finset X) (hx : x ∈ A) :
    upperSum (rankingEdge l x) A = rankingChoice l A x := by
  by_cases hA : A ⊆ lowerContour l x
  · unfold upperSum
    rw [Finset.sum_eq_single (lowerContour l x)]
    · simp [rankingEdge, self_mem_lowerContour hl x, rankingChoice, hA, hx]
    · intro B hB hne
      simp [rankingEdge, hne]
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)).elim
  · have hz : upperSum (rankingEdge l x) A = 0 := by
      unfold upperSum
      apply Finset.sum_eq_zero
      intro B hB
      have hne : B ≠ lowerContour l x := by
        intro h
        exact hA (h ▸ (Finset.mem_filter.mp hB).2)
      simp [rankingEdge, hne]
    rw [hz]
    simp [rankingChoice, hA]
end Falmagne
