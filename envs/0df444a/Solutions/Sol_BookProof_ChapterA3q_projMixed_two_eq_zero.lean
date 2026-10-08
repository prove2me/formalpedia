-- Prove2me | solution 1 for BookProof.ChapterA3q.projMixed_two_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:04:14.67242+00:00
-- url     : https://prove2.me/submissions/9254d343-5da8-496b-9893-abf06160a642

import Definitions.Def_ChapterA3q
import Mathlib
set_option autoImplicit false
open Matrix
open scoped BigOperators

namespace BookProof.ChapterA3p
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem projSym_add_projAnti_two :
    projSym 2 + projAnti 2 = 1 := by
  ext a b; simp only [projSym, Nat.factorial_two, Nat.cast_ofNat, projAnti, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul] ;
  unfold permMat signC;
  rw [ Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum ] ; norm_cast;
  erw [ show ( Finset.univ.val : Multiset ( Equiv.Perm ( Fin 2 ) ) )
          = { Equiv.refl ( Fin 2 ), Equiv.swap 0 1 } by decide ] ; norm_num ; ring;
  exact if_congr ( by aesop ) rfl rfl
end BookProof.ChapterA3p

open BookProof.ChapterA3 BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q
open BookProof.ChapterA3p

theorem solution : projMixed 2 = 0 := by
  unfold projMixed
  rw [← projSym_add_projAnti_two]; abel

#print axioms solution
