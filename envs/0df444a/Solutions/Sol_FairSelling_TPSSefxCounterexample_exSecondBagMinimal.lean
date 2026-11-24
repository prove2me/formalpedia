-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exSecondBagMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:38.557776+00:00
-- url     : https://prove2.me/submissions/1cc0a83e-ad2c-4bff-80ea-7c4d2c775e49

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exp_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_sum23
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_three
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exp_three

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution :
    vbarSum exv exp {2, 3} = 24 ∧
      vbarSum exv exp ({2, 3} \ {2}) < 20 ∧ vbarSum exv exp ({2, 3} \ {3}) < 20 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold vbarSum vbar
    rw [sum23]
    norm_num [exv_two, exv_three, exp_two, exp_three]
  · rw [show ({2, 3} : Finset Gd) \ {2} = {3} by decide]
    unfold vbarSum vbar
    norm_num [exv_three, exp_three]
  · rw [show ({2, 3} : Finset Gd) \ {3} = {2} by decide]
    unfold vbarSum vbar
    norm_num [exv_two, exp_two]
end FairSelling.TPSSefxCounterexample
