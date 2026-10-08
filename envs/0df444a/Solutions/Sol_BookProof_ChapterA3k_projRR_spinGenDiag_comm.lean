-- Prove2me | solution 1 for BookProof.ChapterA3k.projRR_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:29:42.716995+00:00
-- url     : https://prove2.me/submissions/3288a2bb-987f-4b54-bbca-5763d656e33b

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

private theorem spin_comm_local (μ ν : Fin 4) :
    chir * spinGen μ ν = spinGen μ ν * chir := by
  unfold spinGen
  rw [← mul_assoc, anti μ, neg_mul, mul_assoc, anti ν]
  simp [mul_assoc]

private theorem proj_comm_local (μ ν : Fin 4) :
    projChirR * spinGen μ ν = spinGen μ ν * projChirR := by
  simp only [projChirR, smul_mul_assoc, mul_smul_comm,
    add_mul, mul_add, one_mul, mul_one, spin_comm_local μ ν]

theorem solution (μ ν : Fin 4) :
    projRR * spinGenDiag μ ν = spinGenDiag μ ν * projRR := by
  simp only [projRR, spinGenDiag, mul_add, add_mul, ← Matrix.mul_kronecker_mul,
    mul_one, one_mul, proj_comm_local μ ν]

#print axioms solution
