-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.stoneTransfer_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T04:01:10.807828+00:00
-- url     : https://prove2.me/submissions/dee018fa-7a30-4d34-b5d9-12a416c57f00

import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstReducedTransfer



open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {Om}
variable (Om)
variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H) (Om : H →L[ℂ] H)
variable (hcomm : ∀ (t : ℝ) (y : H), T.stoneU t (Om y) = Om (T.stoneU t y))

theorem solution (t : ℝ) : Function.Bijective (stoneTransfer T Om hcomm t) := by
  have key : ∀ s r : ℝ, ∀ c : Cohomology Om,
      stoneTransfer T Om hcomm s (stoneTransfer T Om hcomm r c) = stoneTransfer T Om hcomm (s + r) c := by
    intro s r c
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    simp only [stoneTransfer, transfer, reducedMap]
    erw [Submodule.mapQ_apply, Submodule.mapQ_apply]
    congr 1
    ext
    simpa using T.stoneU_apply_stoneU s r (x : H)
  have zero : ∀ c : Cohomology Om, stoneTransfer T Om hcomm 0 c = c := by
    intro c
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    simp only [stoneTransfer, transfer, reducedMap]
    erw [Submodule.mapQ_apply]
    congr 1
    ext
    simp
  refine ⟨fun a b h => ?_, fun c => ⟨stoneTransfer T Om hcomm (-t) c, ?_⟩⟩
  · have := congrArg (stoneTransfer T Om hcomm (-t)) h
    rwa [key, key, neg_add_cancel, zero, zero] at this
  · rw [key, add_neg_cancel, zero]
