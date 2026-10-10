-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.transfer_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:59:47.602918+00:00
-- url     : https://prove2.me/submissions/fdf3f4d1-42f4-44b8-b079-8255e69ca72b

-- Generated from ChapterBrstReducedTransfer.lean — solution of BookProof.BrstReducedTransfer.transfer_comp
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
theorem solution (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (s t : ℝ) :
    (transfer Om U hcomm s).comp (transfer Om U hcomm t) = transfer Om U hcomm (s + t) := by

  refine LinearMap.ext fun c => ?_
  induction c using Submodule.Quotient.induction_on with
  | H x =>
    simp only [LinearMap.comp_apply, transfer_mk]
    congr 1
    exact Subtype.ext (hgroup s t x)
