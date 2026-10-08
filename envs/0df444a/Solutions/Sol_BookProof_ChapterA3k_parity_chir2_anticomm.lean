-- Prove2me | solution 1 for BookProof.ChapterA3k.parity_chir2_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:11:32.614997+00:00
-- url     : https://prove2.me/submissions/eb332e1e-9768-4c1d-bc8c-6c477b1ade15

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.parity_chir2_anticomm
import Mathlib
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3
open BookProof.ChapterA3j
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

private theorem anti (μ : Fin 4) :
    chir * mgamma μ = -(mgamma μ * chir) := by
  have hz : mgamma5Z * mgammaZ μ = -(mgammaZ μ * mgamma5Z) := by
    fin_cases μ <;> decide
  change ((Int.castRingHom ℂ).mapMatrix mgamma5Z) *
      ((Int.castRingHom ℂ).mapMatrix (mgammaZ μ)) =
        -(((Int.castRingHom ℂ).mapMatrix (mgammaZ μ)) *
          ((Int.castRingHom ℂ).mapMatrix mgamma5Z))
  simpa only [map_mul, map_neg] using
    congrArg ((Int.castRingHom ℂ).mapMatrix) hz

private theorem parity_anti : mgamma 0 * chir = -(chir * mgamma 0) := by
  have h := anti 0
  rw [h, neg_neg]

theorem solution : parityDiag * chir2 = -(chir2 * parityDiag) := by
  simp only [parityDiag, chir2, ← Matrix.mul_kronecker_mul, mul_one, one_mul,
    parity_anti, neg_left, neg_right]

#print axioms solution
