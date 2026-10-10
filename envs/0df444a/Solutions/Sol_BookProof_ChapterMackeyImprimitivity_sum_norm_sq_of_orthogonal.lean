-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.sum_norm_sq_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:29:30.098767+00:00
-- url     : https://prove2.me/submissions/ad85626d-10fd-423c-9ccf-0aca6b0d3f2a

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.sum_norm_sq_of_orthogonal
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity



open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {f : X → E} {ψ : E} (hsum : ∑ x, f x = ψ)
    (horth : ∀ x y, x ≠ y → ⟪f x, f y⟫_ℂ = 0) :
    ∑ x : X, ‖f x‖ ^ 2 = ‖ψ‖ ^ 2 := by

  have hip : ⟪ψ, ψ⟫_ℂ = ∑ x, ⟪f x, f x⟫_ℂ := by
    rw [← hsum, sum_inner]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [inner_sum, Finset.sum_eq_single x]
    · intro y _ hy
      exact horth x y (Ne.symm hy)
    · intro h; simp at h
  have h2 := congrArg (RCLike.re (K := ℂ)) hip
  rw [map_sum] at h2
  simp only [inner_self_eq_norm_sq] at h2
  exact h2.symm
