-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.transfer_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:59:25.709278+00:00
-- url     : https://prove2.me/submissions/b0051e1b-9a8a-4eb0-8941-501c30492b90

-- Generated from ChapterBrstReducedTransfer.lean — solution of BookProof.BrstReducedTransfer.transfer_zero
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.BrstReducedTransfer




open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (Om : H →L[ℂ] H)
variable {Om}
variable (Om)
variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))


@[simp] private theorem transfer_mk (t : ℝ) (x : physicalStates Om) :
    transfer Om U hcomm t (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk ⟨U t x, physicalStates_invariant (hcomm t) x x.2⟩ := rfl

set_option maxHeartbeats 1000000 in
theorem solution (hzero : ∀ x : H, U 0 x = x) :
    transfer Om U hcomm 0 = LinearMap.id := by

  refine LinearMap.ext fun c => ?_
  induction c using Submodule.Quotient.induction_on with
  | H x =>
    rw [transfer_mk, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (hzero x)
