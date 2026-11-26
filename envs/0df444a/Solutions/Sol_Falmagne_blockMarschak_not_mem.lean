-- Prove2me | solution 1 for Falmagne.blockMarschak_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:18.30047+00:00
-- url     : https://prove2.me/submissions/b46d12ff-5002-4276-87e0-1fd8039eea35

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Conservation
public import Theorems.Thm_Falmagne_mem_lowerContour
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_nil
attribute [local simp] Falmagne.mem_lowerContour
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil



set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution (p : Finset X → X → ℝ) (hp : IsChoiceRule p)
    (A : Finset X) (x : X) (hx : x ∉ A) :
    blockMarschak p x A = -blockMarschak p x (insert x A) := by
  classical
  let S := univ.filter (fun B : Finset X => A ⊆ B)
  let T := univ.filter (fun B : Finset X => insert x A ⊆ B)
  have hTS : T ⊆ S := by
    intro B hB
    simp only [T, S, mem_filter, mem_univ, true_and] at hB ⊢
    exact (subset_insert x A).trans hB
  have hrestrict : (∑ B ∈ S, (-1 : ℝ) ^ (B \ A).card * p B x) =
      ∑ B ∈ T, (-1 : ℝ) ^ (B \ A).card * p B x := by
    symm
    apply sum_subset hTS
    intro B hBS hBT
    have hxB : x ∉ B := by
      intro hxB
      apply hBT
      simp only [T, mem_filter, mem_univ, true_and]
      exact insert_subset hxB ((mem_filter.mp hBS).2)
    simp [hp.2.1 B x hxB]
  change (∑ B ∈ S, (-1 : ℝ) ^ (B \ A).card * p B x) =
    -(∑ B ∈ T, (-1 : ℝ) ^ (B \ insert x A).card * p B x)
  rw [hrestrict, ← sum_neg_distrib]
  apply sum_congr rfl
  intro B hBT
  have hxB : x ∈ B := (mem_filter.mp hBT).2 (mem_insert_self x A)
  have hd : B \ A = insert x (B \ insert x A) := by
    ext y
    simp only [mem_sdiff, mem_insert]
    constructor
    · intro hy
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ⟨hy.1, by simpa [hyx] using hy.2⟩
    · intro hy
      rcases hy with rfl | hy
      · exact ⟨hxB, hx⟩
      · exact ⟨hy.1, fun hyA => hy.2 (Or.inr hyA)⟩
  have hnot : x ∉ B \ insert x A := by simp
  rw [hd, card_insert_of_notMem hnot, pow_succ]
  ring
end Falmagne
