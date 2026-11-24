-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.out1_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:30:31.453929+00:00
-- url     : https://prove2.me/submissions/c95d7f18-18ed-4baf-a381-06206467a164

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
theorem _root_.solution : (out1 N).Valid (price N) := by
  refine ⟨sold_keptFun_disj N, keptFun_disj N, ?_, ?_⟩
  · intro j; simp only [out1]; split <;> norm_num
  · simp only [out1, price_sold]
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (N + 1)) (fun _ => (1 : ℝ))]
    simp
end FairSelling.EqualProceedsExampleThree
