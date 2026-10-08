-- Prove2me | solution 1 for BookProof.ChapterA3k.parityDiag_sq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:11:27.589972+00:00
-- url     : https://prove2.me/submissions/3ca54ad0-5d3f-47e8-b8e2-e823e8a182d1

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.parityDiag_sq
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterA3k


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

private theorem neg_left (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  simpa only [neg_one_smul] using Matrix.smul_kronecker (-1 : ℂ) A B

private theorem neg_right (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  simpa only [neg_one_smul] using Matrix.kronecker_smul (-1 : ℂ) A B

private theorem gamma_sq : mgamma 0 * mgamma 0 = -1 := by
  have hz : mgammaZ 0 * mgammaZ 0 = -1 := by decide
  change ((Int.castRingHom ℂ).mapMatrix (mgammaZ 0)) *
    ((Int.castRingHom ℂ).mapMatrix (mgammaZ 0)) = -1
  simpa only [map_mul, map_neg, map_one] using
    congrArg ((Int.castRingHom ℂ).mapMatrix) hz

theorem solution : parityDiag * parityDiag = 1 := by
  simp only [parityDiag, ← Matrix.mul_kronecker_mul, gamma_sq,
    neg_left, neg_right, neg_neg, Matrix.one_kronecker_one]

#print axioms solution
