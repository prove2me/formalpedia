-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exTPS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:27.554516+00:00
-- url     : https://prove2.me/submissions/732583b9-cf2a-4d52-90a4-1e4ada0b01ad

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_nonneg
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_zero
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_zero
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exPS
import Theorems.Thm_FairSelling_TPS_eq_PS_of_top

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
theorem _root_.solution : TPS 2 exv exp = 30 := by
  rw [TPS_eq_PS_of_top exv exp exp_nonneg (s := 19)
    (by intro g; fin_cases g <;> norm_num [exv]) ?_, exPS]
  unfold truncSum
  norm_num [Fin.sum_univ_four, exv_zero, exv_one, exv_two, exv_three, exp_zero, exp_one, exp_two, exp_three]
end FairSelling.TPSSefxCounterexample
