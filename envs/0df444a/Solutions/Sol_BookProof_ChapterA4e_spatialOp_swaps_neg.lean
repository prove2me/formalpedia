-- Prove2me | solution 1 for BookProof.ChapterA4e.spatialOp_swaps_neg
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:58:06.142162+00:00
-- url     : https://prove2.me/submissions/14bde979-5874-4e6d-8716-4d3c7a35fbf5

-- Generated from ChapterA4e.lean — theorem BookProof.ChapterA4e.spatialOp_swaps_neg
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4e
open BookProof.ChapterA4e


open Matrix


open BookProof.ChapterA3 BookProof.ChapterA5

set_option maxHeartbeats 2000000 in
theorem solution (j : Fin 3) :
    projNeg * spatialOp j = spatialOp j * projPos := by
  fin_cases j <;> ext r c <;>
  fin_cases r <;> fin_cases c <;>
    norm_num [projPos, projNeg, enSign, spatialOp, coeffMass1Z,
      coeffBoostZ, spatialIdx, mgammaZ, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.ofNat, Fin.succ,
      Matrix.smul_apply, Matrix.map_apply, RingHom.mapMatrix_apply,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.inv_re,
      Complex.inv_im, Complex.normSq]

#print axioms solution
