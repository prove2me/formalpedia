-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.util_out2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:31:24.156535+00:00
-- url     : https://prove2.me/submissions/6aea7d33-e1d5-459e-8f91-21f7c39f964f

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
theorem _root_.solution (j : Fin (N + 1)) : (1 : ℝ) / ((N : ℝ) + 1) ≤ util (val N) (out2 N) j := by
  unfold util out2 keptFun
  by_cases hj : j = 0
  · simp [hj]
  · have hv : val N j = 1 := by simp [val, hj]
    simp only [hj, if_false, Finset.sum_singleton, hv]
    linarith
end FairSelling.EqualProceedsExampleThree
