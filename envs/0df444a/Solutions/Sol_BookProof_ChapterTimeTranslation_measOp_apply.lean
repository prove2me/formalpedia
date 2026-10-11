-- Prove2me | solution 1 for BookProof.ChapterTimeTranslation.measOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:33:59.654317+00:00
-- url     : https://prove2.me/submissions/5ddde374-2d56-4a13-99ab-742109930c88

-- Generated from ChapterTimeTranslation.lean — solution of BookProof.ChapterTimeTranslation.measOp_apply
import Mathlib
import Definitions.Def_ChapterTimeTranslation
import Definitions.Def_ChapterReconstruct
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterTimeTranslation



open scoped BigOperators
open Finset Matrix
open BookProof.ChapterReconstruct


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (k l : Fin n) :
    measOp U a k l = U k a * (starRingEnd ℂ) (U l a) := by

  unfold measOp;
  simp only [proj, mul_apply, of_apply, mul_ite, mul_one, mul_zero, conjTranspose_apply,
      RCLike.star_def];
  rw [ Finset.sum_eq_single a ] <;> aesop
