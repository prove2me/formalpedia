-- Prove2me | solution 1 for BookProof.ChapterA.cembed_realCommutes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:46:07.700017+00:00
-- url     : https://prove2.me/submissions/6683441b-0711-453a-a312-1b7def8d363e

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.cembed_realCommutes
import Mathlib
import Definitions.Def_ChapterA2c
import Theorems.Thm_BookProof_ChapterA_cembed_apply
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (c : ℂ) :
    RealCommutes M (cembed c) := by

  intro m hm x
  rw [cembed_apply, cembed_apply, map_smul]
