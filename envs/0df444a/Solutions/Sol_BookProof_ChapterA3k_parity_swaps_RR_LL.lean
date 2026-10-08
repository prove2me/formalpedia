-- Prove2me | solution 1 for BookProof.ChapterA3k.parity_swaps_RR_LL
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:11:36.269091+00:00
-- url     : https://prove2.me/submissions/a37c6ecc-55dc-4b0c-9e75-58d159ae6e82

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.parity_swaps_RR_LL
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

private theorem parity_swap_local : mgamma 0 * projChirL = projChirR * mgamma 0 := by
  have h : mgamma 0 * chir = -(chir * mgamma 0) := by
    rw [anti 0, neg_neg]
  simp only [projChirL, projChirR, smul_mul_assoc, mul_smul_comm,
    add_mul, mul_sub, mul_one, one_mul, h, smul_neg]
  simp only [sub_neg_eq_add]

theorem solution : parityDiag * projLL = projRR * parityDiag := by
  simp only [parityDiag, projLL, projRR, ← Matrix.mul_kronecker_mul, parity_swap_local]

#print axioms solution
