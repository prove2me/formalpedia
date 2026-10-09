-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.inner_block_im_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:58:39.449588+00:00
-- url     : https://prove2.me/submissions/d2d8014e-df4d-468e-9431-61a2e326b852

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.inner_block_im_eq_zero
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (a : ℕ → ℕ → ℂ) (u : ℕ → ℂ) (hherm : IsHermitianKernel a)
    (N : ℕ) :
    (∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) *
        ∑ k ∈ range (N + 1), a n k * u k).im = 0 := by

  set Q : ℂ := ∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) * ∑ k ∈ range (N + 1), a n k * u k
    with hQ
  have hexp : Q = ∑ n ∈ range (N + 1), ∑ k ∈ range (N + 1),
      (starRingEnd ℂ) (u n) * (a n k * u k) := by
    rw [hQ]; simp [Finset.mul_sum]
  have hconj : (starRingEnd ℂ) Q = Q := by
    rw [hexp]
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hherm, Complex.conj_conj]
    ring
  have := Complex.conj_eq_iff_im.mp hconj
  simpa [hQ] using this
