-- Prove2me | solution 1 for BookProof.ChapterA3k.parity_swaps_LL_RR
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:11:34.481132+00:00
-- url     : https://prove2.me/submissions/79bd623c-3618-4c2d-a436-ba7ca584cf8c

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.parity_swaps_LL_RR
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

private theorem parity_swap_local : mgamma 0 * projChirR = projChirL * mgamma 0 := by
  have h : mgamma 0 * chir = -(chir * mgamma 0) := by
    rw [anti 0, neg_neg]
  simp only [projChirL, projChirR, smul_mul_assoc, mul_smul_comm,
    mul_add, sub_mul, mul_one, one_mul, h, smul_neg]
  rfl

theorem solution : parityDiag * projRR = projLL * parityDiag := by
  simp only [parityDiag, projLL, projRR, ← Matrix.mul_kronecker_mul, parity_swap_local]

#print axioms solution
