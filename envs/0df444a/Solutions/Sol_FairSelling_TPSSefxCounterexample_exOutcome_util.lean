-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exOutcome_util
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:06.130978+00:00
-- url     : https://prove2.me/submissions/7da940a2-c9c1-4d3e-a3f3-219838c5dd09

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_sum23
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_one
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_three

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution : util exv exOutcome 0 = 36 ∧ util exv exOutcome 1 = 24 := by
  constructor
  · unfold util exOutcome
    norm_num [exv_one]
  · unfold util exOutcome
    show (∑ g ∈ ({2, 3} : Finset Gd), exv g) + 0 = 24
    rw [sum23]
    norm_num [exv_two, exv_three]
end FairSelling.TPSSefxCounterexample
