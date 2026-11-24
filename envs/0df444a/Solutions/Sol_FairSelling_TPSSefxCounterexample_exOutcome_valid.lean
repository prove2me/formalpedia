-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exOutcome_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:50.241971+00:00
-- url     : https://prove2.me/submissions/fe550946-a7f9-4f51-9bef-844a45ebd127

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
theorem _root_.solution : exOutcome.Valid exp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> decide +kernel
  · intro j k hjk; fin_cases j <;> fin_cases k <;> simp_all <;> decide +kernel
  · intro j; fin_cases j <;> norm_num [exOutcome]
  · norm_num [Fin.sum_univ_two, exOutcome, exp]
end FairSelling.TPSSefxCounterexample
