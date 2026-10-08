-- Prove2me | solution 1 for BookProof.ChapterA3p.sum_signC_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:19:40.100948+00:00
-- url     : https://prove2.me/submissions/164a3678-623b-470f-9602-9a56bdb76150

-- Generated from ChapterA3p.lean — theorem BookProof.ChapterA3p.sum_signC_eq_zero
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
import Mathlib
import Definitions.Def_ChapterA3p
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3o
open BookProof.ChapterA3p


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o

namespace LocalChapterA3p
open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
theorem sum_signC_eq_zero {N : ℕ} (hN : 2 ≤ N) :
    ∑ σ : Equiv.Perm (Fin N), signC σ = 0 := by
  have h_transposition : ∃ t : Equiv.Perm (Fin N), Equiv.Perm.sign t = -1 := by
    exact ⟨ Equiv.swap ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩, by simp ⟩;
  obtain ⟨ t, ht ⟩ := h_transposition;    have := Equiv.sum_comp ( Equiv.mulLeft t ) ( fun x =>
      signC x ) ; simp_all only [signC, Equiv.coe_mulLeft, Equiv.Perm.sign_mul, neg_mul, one_mul,
          Units.val_neg, Int.cast_neg, Finset.sum_neg_distrib] ;
  linear_combination' -this / 2

end LocalChapterA3p


theorem solution {N : ℕ} (hN : 2 ≤ N) :
    ∑ σ : Equiv.Perm (Fin N), signC σ = 0 := by
  exact LocalChapterA3p.sum_signC_eq_zero hN

#print axioms solution
