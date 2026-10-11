-- Prove2me | solution 1 for BookProof.ChapterDeterministic.measOp_mul_proj_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:32:57.977507+00:00
-- url     : https://prove2.me/submissions/5f490f9c-399c-43f5-8552-e92ed1ec6e81

-- Generated from ChapterDeterministic.lean — solution of BookProof.ChapterDeterministic.measOp_mul_proj_apply
import Mathlib
import Definitions.Def_ChapterDeterministic
import Theorems.Thm_BookProof_ChapterTimeTranslation_measOp_apply
import Definitions.Def_ChapterReconstruct
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterTimeTranslation
open BookProof.ChapterDeterministic



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) :
    (measOp U b * proj a) i j =
      if j = a then U i b * (starRingEnd ℂ) (U a b) else 0 := by

  rw [Matrix.mul_apply];
  rw [ Finset.sum_eq_single a ] <;> simp +contextual [ proj, measOp_apply ]
