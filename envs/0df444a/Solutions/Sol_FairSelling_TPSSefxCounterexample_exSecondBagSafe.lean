-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exSecondBagSafe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:42:42.391547+00:00
-- url     : https://prove2.me/submissions/76f59f18-8a29-4f54-ae1e-8d1fba0972b3

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_sum23
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_one
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_three
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_one
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_three

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution :
    vbarSum (exV 0) exp (exOutcome.kept 1) + exOutcome.money 1
      ≤ vbarSum (exV 0) exp (exOutcome.kept 0) + exOutcome.money 0 := by
  show (∑ g ∈ ({2, 3} : Finset Gd), vbar exv exp g) + 0
      ≤ (∑ g ∈ ({1} : Finset Gd), vbar exv exp g) + 18
  rw [sum23]
  unfold vbar
  norm_num [exv_one, exv_two, exv_three, exp_one, exp_two, exp_three]
end FairSelling.TPSSefxCounterexample
