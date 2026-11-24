-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:19.645834+00:00
-- url     : https://prove2.me/submissions/6d38710f-d35b-4f89-9cf0-32d4f637feee

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
theorem _root_.solution : ∀ g, 0 ≤ exp g := by
  intro g; fin_cases g <;> norm_num [exp]
end FairSelling.TPSSefxCounterexample
