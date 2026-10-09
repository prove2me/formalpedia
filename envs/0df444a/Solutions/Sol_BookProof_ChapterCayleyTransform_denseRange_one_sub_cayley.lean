-- Prove2me | solution 1 for BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:05:39.436983+00:00
-- url     : https://prove2.me/submissions/ab4a8a41-f319-476d-8bc4-e74c49e64b3f

-- Generated from ChapterCayleyTransform.lean — solution of BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley
import Mathlib
import Definitions.Def_ChapterCayleyTransform
import Theorems.Thm_BookProof_ChapterCayleyTransform_range_one_sub_cayley
open BookProof.ChapterCayleyTransform



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution :
    DenseRange (fun y : H => y - cayley T y) := by

  rw [DenseRange, range_one_sub_cayley]
  exact T.denseDomain
