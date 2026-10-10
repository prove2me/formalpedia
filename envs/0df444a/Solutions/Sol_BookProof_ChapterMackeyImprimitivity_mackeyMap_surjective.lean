-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.mackeyMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:32:50.012354+00:00
-- url     : https://prove2.me/submissions/82ed7fba-2af6-4ce3-9a03-1c3849a0a3ca

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.mackeyMap_surjective
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_ImprimitivitySystem_U_inv_apply
open BookProof.ChapterMackeyImprimitivity



open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

set_option maxHeartbeats 1000000 in
theorem solution (hs : ∀ x, s x • x₀ = x) {f : X → E}
    (hf : f ∈ InducedSpace S x₀) : ∃ ψ : E, mackeyMap S s ψ = f := by

  refine ⟨∑ x : X, S.U (s x) (f x), ?_⟩
  -- each summand lies in the `x`-th fibre
  have hfib : ∀ x : X, S.p x (S.U (s x) (f x)) = S.U (s x) (f x) := by
    intro x
    have h := S.covariant (s x) x₀ (f x)
    rw [hf x, hs x] at h
    exact h.symm
  funext y
  have hsum : S.p y (∑ x : X, S.U (s x) (f x)) = S.U (s y) (f y) := by
    rw [map_sum, Finset.sum_eq_single y]
    · exact hfib y
    · intro x _ hx
      rw [← hfib x]
      exact S.orthogonal y x (Ne.symm hx) _
    · intro h; simp at h
  simp only [mackeyMap, hsum, S.U_inv_apply]
