-- Prove2me | solution 1 for BookProof.FockQuadratic.hopOp_pairing
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:52:23.013283+00:00
-- url     : https://prove2.me/submissions/bf8ef2af-405f-45e4-95d1-07ea3cbcd516

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.hopOp_pairing
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Theorems.Thm_BookProof_FockQuadratic_tsum_hop_reindex
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable {ω : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (hQP : deg Q + deg P ≤ 2) (x y : maxDom (sig ω)) :
    (inner ℂ (hopOp hω P Q hPQ x : L2I (Idx ι)) (y : L2I (Idx ι)) : ℂ)
      = inner ℂ (x : L2I (Idx ι)) (hopOp hω Q P hQP y : L2I (Idx ι)) := by

  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_hop_reindex (P := P) (Q := Q) ?_ ?_ ?_
  · intro b hb
    simp [RCLike.inner_apply, amp_eq_zero_of_not_le hb]
  · intro a ha
    simp [RCLike.inner_apply, amp_eq_zero_of_not_le ha]
  · intro a ha
    simp only [RCLike.inner_apply, hopOp_coe, map_mul, Complex.conj_ofReal]
    rw [amp_symm ha, tgt_tgt ha]
    ring
