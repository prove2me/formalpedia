-- Prove2me | solution 1 for BookProof.ChapterA4g.rotGen_enSign_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:50:02.06428+00:00
-- url     : https://prove2.me/submissions/c276611d-a7a0-4bea-85ca-38039775f6c9

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.rotGen_enSign_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterA5
open BookProof.ChapterA4e
open BookProof.ChapterA5
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 4000000 in
private theorem rotation_comm (i j : Fin 3) :
    rotGen i j * enSign = enSign * rotGen i j := by
  have hz : rotGenZ i j * BookProof.ChapterA5.coeffMass1Z =
      BookProof.ChapterA5.coeffMass1Z * rotGenZ i j := by
    fin_cases i <;> fin_cases j <;> ext r c <;> fin_cases r <;> fin_cases c <;>
      norm_num [rotGenZ, BookProof.ChapterA5.coeffMass1Z,
        BookProof.ChapterA5.spatialIdx, mgammaZ, Matrix.mul_apply,
        Fin.sum_univ_succ, Fin.ofNat, Fin.succ]
  change (rotGenZ i j).map (Int.castRingHom ℂ) *
      BookProof.ChapterA5.coeffMass1Z.map (Int.castRingHom ℂ) =
      BookProof.ChapterA5.coeffMass1Z.map (Int.castRingHom ℂ) *
      (rotGenZ i j).map (Int.castRingHom ℂ)
  rw [← Matrix.map_mul, ← Matrix.map_mul, hz]

theorem solution (i j : Fin 3) :
    rotGen i j * enSign = enSign * rotGen i j := by
  exact rotation_comm i j

#print axioms solution
