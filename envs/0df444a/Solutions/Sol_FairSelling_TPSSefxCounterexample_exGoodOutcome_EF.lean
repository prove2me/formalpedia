-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exGoodOutcome_EF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:56.998992+00:00
-- url     : https://prove2.me/submissions/ba38f3a8-1025-443b-87cd-f0bcddc400a0

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_zero
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_zero
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_sum23
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_zero
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_one
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_three
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_zero
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_one
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_three

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution : EF exV exp exGoodOutcome := by
  intro i j
  have h0 : vbarSum (exV i) exp (exGoodOutcome.kept 0) + exGoodOutcome.money 0 = 30 := by
    show (∑ g ∈ ({1} : Finset Gd), vbar exv exp g) + 12 = 30
    unfold vbar
    norm_num [exv_one, exp_one]
  have h1 : vbarSum (exV i) exp (exGoodOutcome.kept 1) + exGoodOutcome.money 1 = 30 := by
    show (∑ g ∈ ({2, 3} : Finset Gd), vbar exv exp g) + 6 = 30
    rw [sum23]
    unfold vbar
    norm_num [exv_two, exv_three, exp_two, exp_three]
  fin_cases j <;> fin_cases i <;> simp_all
end FairSelling.TPSSefxCounterexample
