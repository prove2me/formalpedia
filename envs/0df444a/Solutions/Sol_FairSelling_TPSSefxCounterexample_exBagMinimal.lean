-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exBagMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:28.655197+00:00
-- url     : https://prove2.me/submissions/c817098c-f75b-4fb4-9f33-ed66b282b679

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_zero
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_zero
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exBagValue
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_zero
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_one
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_zero
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_one

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution :
    20 ≤ vbarSum exv exp {0, 1} ∧
      vbarSum exv exp ({0, 1} \ {0}) < 20 ∧ vbarSum exv exp ({0, 1} \ {1}) < 20 := by
  refine ⟨by rw [exBagValue]; norm_num, ?_, ?_⟩
  · rw [show ({0, 1} : Finset Gd) \ {0} = {1} by decide]
    unfold vbarSum vbar
    norm_num [exv_one, exp_one]
  · rw [show ({0, 1} : Finset Gd) \ {1} = {0} by decide]
    unfold vbarSum vbar
    norm_num [exv_zero, exp_zero]
end FairSelling.TPSSefxCounterexample
