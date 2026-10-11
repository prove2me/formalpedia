-- Prove2me | solution 1 for BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministicCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:32:59.287986+00:00
-- url     : https://prove2.me/submissions/f65555f3-bdc8-475a-b72c-5878d22b4b63

-- Generated from ChapterDeterministic.lean — solution of BookProof.ChapterDeterministic.commute_proj_measOp_iff_isDeterministicCol
import Mathlib
import Definitions.Def_ChapterDeterministic
import Theorems.Thm_BookProof_ChapterDeterministic_proj_mul_measOp_apply
import Theorems.Thm_BookProof_ChapterDeterministic_measOp_mul_proj_apply
import Theorems.Thm_BookProof_ChapterTimeTranslation_measOp_apply
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterReconstruct
import Definitions.Def_ChapterTimeTranslation
open BookProof.ChapterDeterministic



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct BookProof.ChapterTimeTranslation


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution
    (U : Matrix (Fin n) (Fin n) ℂ) (b : Fin n) :
    (∀ a : Fin n, Commute (proj a) (measOp U b)) ↔ IsDeterministicCol U b := by

  constructor;
  · intro h_comm l m hlm;
    convert congr_arg (fun x : ℂ => starRingEnd ℂ x)
      (congr_fun (congr_fun (h_comm m) m) l) using 1
      <;> simp only [proj]
    · simp [Matrix.mul_apply, measOp_apply]
    · have h := measOp_mul_proj_apply U m b m l
      simp only [proj, hlm, ↓reduceIte] at h
      rw [h]
      simp
  · intro h a
    ext i j
    by_cases hi : i = a <;> by_cases hj : j = a
      <;> simp [*, proj_mul_measOp_apply, measOp_mul_proj_apply]
    · specialize h j a; aesop
    · specialize h i a; aesop
