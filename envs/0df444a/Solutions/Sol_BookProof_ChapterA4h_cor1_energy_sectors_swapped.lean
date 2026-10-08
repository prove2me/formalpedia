-- Prove2me | solution 1 for BookProof.ChapterA4h.cor1_energy_sectors_swapped
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:55:19.932617+00:00
-- url     : https://prove2.me/submissions/f2ff5a9d-767c-42b1-aa31-5015e7930d36

import Mathlib
import Definitions.Def_ChapterA4h
open Matrix BookProof.ChapterA3 BookProof.ChapterA4e BookProof.ChapterA4f BookProof.ChapterA5 BookProof.ChapterA4h
set_option maxHeartbeats 0

theorem solution (j : Fin 3) :
    projPos * spatialOp j = spatialOp j * projNeg := by
  ext a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [projPos, projNeg, enSign, spatialOp, coeffMass1Z, coeffBoostZ,
      spatialIdx, mgammaZ, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.ofNat, Fin.succ,
      Matrix.smul_apply, Matrix.map_apply, RingHom.mapMatrix_apply,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.inv_re,
      Complex.inv_im, Complex.normSq]

#print axioms solution
