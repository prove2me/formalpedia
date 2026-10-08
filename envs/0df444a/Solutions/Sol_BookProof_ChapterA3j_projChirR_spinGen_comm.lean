-- Prove2me | solution 1 for BookProof.ChapterA3j.projChirR_spinGen_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:08:15.459639+00:00
-- url     : https://prove2.me/submissions/4447a99e-77cf-4a00-bf66-ba8076089986

-- Generated from ChapterA3j.lean — theorem BookProof.ChapterA3j.projChirR_spinGen_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3j


open Matrix


open BookProof.ChapterA3

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
theorem solution (μ ν : Fin 4) : projChirR * spinGen μ ν = spinGen μ ν * projChirR := by
  simp only [projChirR, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
    one_mul, mul_one, spin_comm_local μ ν]

#print axioms solution
