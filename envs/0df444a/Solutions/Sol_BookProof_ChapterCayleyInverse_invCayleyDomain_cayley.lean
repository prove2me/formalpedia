-- Prove2me | solution 1 for BookProof.ChapterCayleyInverse.invCayleyDomain_cayley
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:17.465023+00:00
-- url     : https://prove2.me/submissions/49a4d3cf-815c-475b-b317-f532752df86a

-- Generated from ChapterCayleyInverse.lean — solution of BookProof.ChapterCayleyInverse.invCayleyDomain_cayley
import Mathlib
import Definitions.Def_ChapterCayleyInverse
import Theorems.Thm_BookProof_ChapterCayleyTransform_range_one_sub_cayley
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterStoneResolvent
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

theorem solution : invCayleyDomain (cayley T) = T.domain := by
  apply SetLike.ext'
  rw [invCayleyDomain, LinearMap.coe_range]
  exact range_one_sub_cayley T
