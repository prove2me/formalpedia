-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.keptFun_disj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:25.229324+00:00
-- url     : https://prove2.me/submissions/890f8358-4bad-44c7-8a5e-7a5414ed00b8

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
theorem _root_.solution (j k : Fin (N + 1)) (hjk : j ≠ k) :
    Disjoint (keptFun N j) (keptFun N k) := by
  unfold keptFun
  by_cases hj : j = 0 <;> by_cases hk : k = 0 <;> simp [hj, hk, hjk]
end FairSelling.EqualProceedsExampleThree
