-- Prove2me | solution 1 for BookProof.ChapterA4g.rotGenZ_coeffMass1Z_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:37:30.490716+00:00
-- url     : https://prove2.me/submissions/997c0aa7-9f6e-4632-90d5-ac197fdccd76

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.rotGenZ_coeffMass1Z_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA5
open BookProof.ChapterA5
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 4000000 in
theorem solution (i j : Fin 3) :
    rotGenZ i j * coeffMass1Z = coeffMass1Z * rotGenZ i j := by
  fin_cases i <;> fin_cases j <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [rotGenZ, coeffMass1Z, spatialIdx, mgammaZ, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ofNat, Fin.succ]

#print axioms solution

