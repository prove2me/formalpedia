-- Prove2me | solution 1 for BookProof.ChapterA4g.rotGen_projPos_comm
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:47:38.383899+00:00
-- url     : https://prove2.me/submissions/9c0e55bb-73d5-404f-a0f8-a3f8204b2b28

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.rotGen_projPos_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4e
open BookProof.ChapterA4e
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
    rotGen i j * projPos = projPos * rotGen i j := by
  unfold projPos
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_one, one_mul,
    rotation_comm]

#print axioms solution
