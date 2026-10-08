-- Prove2me | solution 1 for BookProof.ChapterA4e.projPos_spatialOp_commutator
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:56:24.090771+00:00
-- url     : https://prove2.me/submissions/226665d9-68a2-4abe-b646-24bfd870b0f9

-- Generated from ChapterA4e.lean — theorem BookProof.ChapterA4e.projPos_spatialOp_commutator
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4e
open BookProof.ChapterA4e


open Matrix


open BookProof.ChapterA3 BookProof.ChapterA5

set_option maxHeartbeats 2000000 in
theorem solution (j : Fin 3) :
    projPos * spatialOp j - spatialOp j * projPos
      = Complex.I • (spatialOp j * enSign) := by
  fin_cases j <;> ext r c <;>
  fin_cases r <;> fin_cases c <;>
    norm_num [projPos, projNeg, enSign, spatialOp, coeffMass1Z,
      coeffBoostZ, spatialIdx, mgammaZ, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.ofNat, Fin.succ,
      Matrix.smul_apply, Matrix.map_apply, RingHom.mapMatrix_apply,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.inv_re,
      Complex.inv_im, Complex.normSq]

#print axioms solution
