-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.flux_identity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:58:40.67958+00:00
-- url     : https://prove2.me/submissions/2fdb4ce7-54c4-458b-8383-41f51624f76c

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.flux_identity
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_inner_block_im_eq_zero
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hherm : IsHermitianKernel a)
    (hrec : LadderRecInf a u z) (N : ℕ) :
    z.im * ∑ n ∈ range (N + 1), ‖u n‖ ^ 2 = (flux a u N).im := by

  have hsplit : ∀ n, z * u n
      = (∑ k ∈ range (N + 1), a n k * u k)
        + ∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1)) := by
    intro n
    rw [← hrec.eqn n, ← (hrec.row n).sum_add_tsum_nat_add (N + 1)]
  have hL : ∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) * (z * u n)
      = z * ((∑ n ∈ range (N + 1), ‖u n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h1 : (starRingEnd ℂ) (u n) * u n = ((‖u n‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      simp [Complex.normSq_eq_norm_sq]
    push_cast at h1
    rw [show (starRingEnd ℂ) (u n) * (z * u n) = z * ((starRingEnd ℂ) (u n) * u n) by ring, h1]
  have hL2 : ∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) * (z * u n)
      = (∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) * ∑ k ∈ range (N + 1), a n k * u k)
        + flux a u N := by
    rw [flux, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hsplit n, mul_add]
  have him := congrArg Complex.im (hL.symm.trans hL2)
  rw [Complex.add_im, inner_block_im_eq_zero a u hherm N, zero_add] at him
  rw [← him, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
