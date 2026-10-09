-- Prove2me | solution 1 for BookProof.ChapterCayleyInverse.oneSubU_cayley_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:04:19.074813+00:00
-- url     : https://prove2.me/submissions/fe089d70-7e7b-42e7-bdaa-2c2af701d954

-- Generated from ChapterCayleyInverse.lean — solution of BookProof.ChapterCayleyInverse.oneSubU_cayley_injective
import Mathlib
import Definitions.Def_ChapterCayleyInverse
import Theorems.Thm_BookProof_ChapterCayleyTransform_one_sub_cayley_injective
open BookProof.ChapterCayleyInverse



open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (V : H ≃ₗᵢ[ℂ] H)
variable (hinj : Function.Injective (oneSubU V))
variable [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution : Function.Injective (oneSubU (cayley T)) := by

  intro a b hab
  exact one_sub_cayley_injective T hab
