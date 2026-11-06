-- Prove2me | solution 2 for BookProof.ChapterMackeyGeneralBase.mackeyMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:00:26.653577+00:00
-- url     : https://prove2.me/submissions/2706d6d8-2ec2-4f2e-834f-c164c3beefca

-- Generated from ChapterMackeyGeneralBase.lean — solution of BookProof.ChapterMackeyGeneralBase.mackeyMap_surjective
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_ImprimitivitySystem_inner_pvm_eq_zero
import Theorems.Thm_BookProof_ChapterOrthogonalSums_summable_of_orthogonal_of_summable_norm_sq
open BookProof.ChapterMackeyGeneralBase

open scoped InnerProductSpace

open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] (hs : ∀ x, s x • x₀ = x) {f : X → E}
    (hf : f ∈ InducedSpace S x₀) : ∃ ψ : E, mackeyMap S s ψ = f := by
  obtain ⟨hfib₀, hsum⟩ := hf
  have hfib : ∀ x : X, S.p x (S.U (s x) (f x)) = S.U (s x) (f x) := by
    intro x
    have h := S.covariant (s x) x₀ (f x)
    rw [hfib₀ x, hs x] at h
    exact h.symm
  have horth : ∀ x y : X, x ≠ y → ⟪S.U (s x) (f x), S.U (s y) (f y)⟫_ℂ = 0 := by
    intro x y hxy
    rw [← hfib x, ← hfib y]
    exact S.inner_pvm_eq_zero hxy _ _
  have hnorm : ∀ x : X, ‖S.U (s x) (f x)‖ = ‖f x‖ := fun x => by simp
  have hsum' : Summable fun x => ‖S.U (s x) (f x)‖ ^ 2 := by
    simpa only [hnorm] using hsum
  obtain ⟨ψ, hψ⟩ := summable_of_orthogonal_of_summable_norm_sq horth hsum'
  refine ⟨ψ, ?_⟩
  funext y
  have hpy : HasSum (fun x => S.p y (S.U (s x) (f x))) (S.p y ψ) := hψ.mapL (S.p y)
  have hpy' : HasSum (fun x => S.p y (S.U (s x) (f x))) (S.U (s y) (f y)) := by
    have h : ∀ x : X, x ≠ y → S.p y (S.U (s x) (f x)) = 0 := by
      intro x hx
      rw [← hfib x]
      exact S.orthogonal y x (Ne.symm hx) _
    have := hasSum_single (f := fun x => S.p y (S.U (s x) (f x))) y h
    rwa [hfib y] at this
  have hval : S.p y ψ = S.U (s y) (f y) := hpy.unique hpy'
  simp [mackeyMap, hval]
