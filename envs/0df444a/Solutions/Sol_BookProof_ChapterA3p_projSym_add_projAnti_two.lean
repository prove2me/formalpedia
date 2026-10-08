-- Prove2me | solution 1 for BookProof.ChapterA3p.projSym_add_projAnti_two
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:19:02.900999+00:00
-- url     : https://prove2.me/submissions/11ea748e-876d-4bb7-a977-77ed376b8034

-- Generated from ChapterA3p.lean — theorem BookProof.ChapterA3p.projSym_add_projAnti_two
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3p
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3p


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o

namespace LocalChapterA3p
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem projSym_add_projAnti_two :
    BookProof.ChapterA3n.projSym 2 + projAnti 2 = 1 := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  classical
  ext a b
  simp only [BookProof.ChapterA3n.projSym, projAnti, Nat.factorial_two, Nat.cast_ofNat,
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


theorem solution :
    projSym 2 + projAnti 2 = 1 := by
  exact LocalChapterA3p.projSym_add_projAnti_two

#print axioms solution
