-- Prove2me | solution 1 for BookProof.ChapterAbelianVonNeumannFinite.commutes_diagonal_iff
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:56:35.017283+00:00
-- url     : https://prove2.me/submissions/67cf982d-8a39-4be1-be29-7b24830a28d1

-- Generated from ChapterAbelianVonNeumannFinite.lean — theorem BookProof.ChapterAbelianVonNeumannFinite.commutes_diagonal_iff
import Mathlib
import Definitions.Def_ChapterAbelianVonNeumannFinite
open BookProof.ChapterAbelianVonNeumannFinite


open Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

namespace BookProof.ChapterAbelianVonNeumannFinite
end BookProof.ChapterAbelianVonNeumannFinite

theorem solution (e : n → ℂ) (he : Function.Injective e) (M : Matrix n n ℂ) :
    M * diagonal e = diagonal e * M ↔ ∃ d : n → ℂ, M = diagonal d := by
  constructor
  · intro h
    refine ⟨fun i => M i i, ?_⟩
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp
    · have hthis := congrFun (congrFun h i) j
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, mul_ite, ite_mul, zero_mul, mul_zero,
        Finset.sum_ite_eq] at hthis
      have hne : e j - e i ≠ 0 := sub_ne_zero.mpr (fun hc => hij (he hc).symm)
      have hzero : M i j * (e j - e i) = 0 := by ring_nf; linear_combination hthis
      have hMij : M i j = 0 := (mul_eq_zero.mp hzero).resolve_right hne
      simp [Matrix.diagonal_apply_ne _ hij, hMij]
  · rintro ⟨d, rfl⟩
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp [mul_comm]

#print axioms solution

