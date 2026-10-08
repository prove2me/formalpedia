-- Prove2me | solution 1 for BookProof.ChapterA3k.parity_swaps_LR_RL
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:29:33.22995+00:00
-- url     : https://prove2.me/submissions/04e8e2da-97cb-47a8-ab2d-46ee73b5db8a

import Mathlib
import Definitions.Def_ChapterA3k
open Matrix
open scoped Kronecker
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

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


private theorem swapL : mgamma 0 * projChirL = projChirR * mgamma 0 := by
  have h : mgamma 0 * chir = -(chir * mgamma 0) := by
    rw [anti 0, neg_neg]
  simp only [projChirL, projChirR, smul_mul_assoc, mul_smul_comm,
    add_mul, mul_sub, mul_one, one_mul, h, smul_neg]
  simp only [sub_neg_eq_add]

private theorem swapR : mgamma 0 * projChirR = projChirL * mgamma 0 := by
  have h : mgamma 0 * chir = -(chir * mgamma 0) := by
    rw [anti 0, neg_neg]
  simp only [projChirL, projChirR, smul_mul_assoc, mul_smul_comm,
    mul_add, sub_mul, mul_one, one_mul, h, smul_neg]
  rfl

theorem solution : parityDiag * projLR = projRL * parityDiag := by
  simp only [parityDiag, projLR, projRL, ← Matrix.mul_kronecker_mul, swapL, swapR]

#print axioms solution
