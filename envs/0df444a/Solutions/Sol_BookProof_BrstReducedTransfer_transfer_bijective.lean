-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.transfer_bijective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:44:23.669169+00:00
-- url     : https://prove2.me/submissions/86451d9d-46d6-4da1-9fc1-8de1550c2fa0

-- Generated from ChapterBrstReducedTransfer.lean — solution of BookProof.BrstReducedTransfer.transfer_bijective
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Theorems.Thm_BookProof_BrstReducedTransfer_transfer_zero
import Theorems.Thm_BookProof_BrstReducedTransfer_transfer_apply_transfer
open BookProof.BrstReducedTransfer




open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (Om : H →L[ℂ] H)
variable {Om}
variable (Om)
variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))

set_option maxHeartbeats 1000000 in
theorem solution (hzero : ∀ x : H, U 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (t : ℝ) :
    Function.Bijective (transfer Om U hcomm t) := by

  constructor
  · intro a b hab
    have h := congrArg (transfer Om U hcomm (-t)) hab
    rw [transfer_apply_transfer Om U hcomm hgroup, transfer_apply_transfer Om U hcomm hgroup,
      neg_add_cancel, transfer_zero Om U hcomm hzero] at h
    simpa using h
  · intro c
    refine ⟨transfer Om U hcomm (-t) c, ?_⟩
    rw [transfer_apply_transfer Om U hcomm hgroup, add_neg_cancel,
      transfer_zero Om U hcomm hzero]
    simp
