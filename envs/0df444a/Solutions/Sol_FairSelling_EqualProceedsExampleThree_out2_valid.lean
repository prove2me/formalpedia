-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.out2_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:30:33.117442+00:00
-- url     : https://prove2.me/submissions/3652507c-f131-4412-95c4-e6206236db46

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_price_sold
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_keptFun_disj
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_sold_keptFun_disj

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleThree
theorem _root_.solution : (out2 N).Valid (price N) := by
  refine ⟨sold_keptFun_disj N, keptFun_disj N, ?_, ?_⟩
  · intro j; simp only [out2]; positivity
  · simp only [out2, price_sold]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [mul_one_div, div_self (by positivity)]
end FairSelling.EqualProceedsExampleThree
