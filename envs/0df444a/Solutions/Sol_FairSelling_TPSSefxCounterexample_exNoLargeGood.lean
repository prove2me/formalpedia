-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exNoLargeGood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:17.674828+00:00
-- url     : https://prove2.me/submissions/9bb86c7a-f789-41f6-b0e7-266b94d8bad8

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution : ∀ g : Gd, exp g < 20 ∧ exv g < 20 := by
  intro g; fin_cases g <;> constructor <;> norm_num [exv, exp]
end FairSelling.TPSSefxCounterexample
