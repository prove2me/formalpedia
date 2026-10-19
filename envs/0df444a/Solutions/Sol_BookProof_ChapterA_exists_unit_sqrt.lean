-- Prove2me | solution 1 for BookProof.ChapterA.exists_unit_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:48:05.607297+00:00
-- url     : https://prove2.me/submissions/3e06768c-124f-424d-a2e9-fe1d993eb384

-- Generated from ChapterA2d.lean — solution of BookProof.ChapterA.exists_unit_sqrt
import Mathlib
import Definitions.Def_ChapterA2d
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) (hc : ‖c‖ = 1) :
    ∃ l : ℂ, l ^ 2 = c ∧ ‖l‖ = 1 := by

  refine ⟨ c ^ ( 1 / 2 : ℂ ), ?_, ?_ ⟩ <;> norm_num [ hc ];
  · rw [ ← Complex.cpow_nat_mul ] ; norm_num;
  · rw [ Complex.norm_cpow_of_imp ] <;> aesop
