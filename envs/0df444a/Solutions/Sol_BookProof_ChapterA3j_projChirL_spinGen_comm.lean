-- Prove2me | solution 1 for BookProof.ChapterA3j.projChirL_spinGen_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:08:13.860608+00:00
-- url     : https://prove2.me/submissions/71e3cd06-23ac-420a-b7fd-67024bea1ca2

-- Generated from ChapterA3j.lean — theorem BookProof.ChapterA3j.projChirL_spinGen_comm
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
theorem solution (μ ν : Fin 4) : projChirL * spinGen μ ν = spinGen μ ν * projChirL := by
  simp only [projChirL, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub,
    one_mul, mul_one, spin_comm_local μ ν]

#print axioms solution
