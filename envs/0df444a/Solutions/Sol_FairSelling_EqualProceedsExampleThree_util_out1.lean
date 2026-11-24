-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.util_out1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:31:18.721293+00:00
-- url     : https://prove2.me/submissions/f4d3b148-2769-41f1-844b-89511d9e8903

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
theorem _root_.solution (j : Fin (N + 1)) : util (val N) (out1 N) j = 1 := by
  unfold util out1 keptFun
  by_cases hj : j = 0 <;> simp [hj, val]
end FairSelling.EqualProceedsExampleThree
