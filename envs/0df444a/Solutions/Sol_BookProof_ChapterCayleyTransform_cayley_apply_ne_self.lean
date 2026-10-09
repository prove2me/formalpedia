-- Prove2me | solution 1 for BookProof.ChapterCayleyTransform.cayley_apply_ne_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:05:00.196983+00:00
-- url     : https://prove2.me/submissions/36e4dcc6-7202-4a62-84fd-c9c288307aa5

-- Generated from ChapterCayleyTransform.lean — solution of BookProof.ChapterCayleyTransform.cayley_apply_ne_self
import Mathlib
import Definitions.Def_ChapterCayleyTransform
import Theorems.Thm_BookProof_ChapterCayleyTransform_one_sub_cayley_injective
open BookProof.ChapterCayleyTransform



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution {y : H} (hy : y ≠ 0) : cayley T y ≠ y := by

  intro h
  refine hy (one_sub_cayley_injective T (show y - cayley T y = 0 - cayley T 0 by simp [h]))
