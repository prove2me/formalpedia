-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:10.500819+00:00
-- url     : https://prove2.me/submissions/9c35abf2-a522-4a60-8fe7-d2af524ec8bd

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
theorem _root_.solution : ∀ g, 0 ≤ exv g := by
  intro g; fin_cases g <;> norm_num [exv]
end FairSelling.TPSSefxCounterexample
