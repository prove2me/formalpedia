-- Prove2me | solution 1 for BookProof.ChapterCayleyTransform.op_eq_cayley
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:05:40.457294+00:00
-- url     : https://prove2.me/submissions/a6a7093a-caee-4a84-8db0-c9efad7f9a0d

-- Generated from ChapterCayleyTransform.lean — solution of BookProof.ChapterCayleyTransform.op_eq_cayley
import Mathlib
import Definitions.Def_ChapterCayleyTransform
import Theorems.Thm_BookProof_ChapterCayleyTransform_add_cayley_shift
open BookProof.ChapterCayleyTransform



open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution (x : T.domain) :
    T.op x = (2 : ℂ)⁻¹ • (T.shift (-1) x + cayley T (T.shift (-1) x)) := by

  rw [add_cayley_shift, smul_smul]
  norm_num
