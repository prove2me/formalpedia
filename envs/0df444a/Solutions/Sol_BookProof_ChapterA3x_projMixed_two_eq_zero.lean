-- Prove2me | solution 1 for BookProof.ChapterA3x.projMixed_two_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:56:09.588547+00:00
-- url     : https://prove2.me/submissions/67797585-cdef-48c5-81ed-1a5ce4c40a4f

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projMixed_two_eq_zero
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

namespace LocalChapterA3p
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem projSym_add_projAnti_two :
    projSym 2 + projAnti 2 = 1 := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  classical
  ext a b
  simp only [projSym, projAnti, Nat.factorial_two, Nat.cast_ofNat,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [hp]
  simp only [Finset.sum_insert (by decide : (1 : Equiv.Perm (Fin 2)) ∉
    {Equiv.swap (0 : Fin 2) 1}), Finset.sum_singleton]
  simp only [permMat, signC, Matrix.of_apply, map_one, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1),
    Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg]
  simp only [Equiv.Perm.coe_one, Function.comp_id]
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num
  all_goals simp_all only [eq_comm]
  all_goals simp only [↓reduceIte]; split_ifs <;> norm_num
end LocalChapterA3p

open LocalChapterA3p

theorem solution : projMixed 2 = 0 := by
  have h := LocalChapterA3p.projSym_add_projAnti_two
  simp only [projMixed]
  rw [show (1 : MN 2) - projSym 2 - projAnti 2 = 1 - (projSym 2 + projAnti 2) by abel, h,
    sub_self]

#print axioms solution
