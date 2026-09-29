-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:35:46.372523+00:00
-- url     : https://prove2.me/submissions/a0c7b761-0395-4f6a-8905-daeb550e3dc1

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.BigOperators

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem solution {κ : Type*} (s : Finset κ) (a : κ → F) :
    ‖∑ k ∈ s, a k‖ ^ 2 = ∑ k ∈ s, ∑ l ∈ s, (inner ℂ (a k) (a l) : ℂ).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [sum_inner, inner_sum, Complex.re_sum, RCLike.re_to_complex]
  rw [Finset.sum_comm]

#print axioms solution
