-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.sold_keptFun_disj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:25.833893+00:00
-- url     : https://prove2.me/submissions/b66f7264-079d-4cc7-bb2e-3977676ab5f4

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleThree
theorem _root_.solution (j : Fin (N + 1)) :
    Disjoint ({0} : Finset (Fin (N + 1))) (keptFun N j) := by
  unfold keptFun
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj, Ne.symm hj]
end FairSelling.EqualProceedsExampleThree
