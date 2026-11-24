-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.sum01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:30.774156+00:00
-- url     : https://prove2.me/submissions/315f50fa-1f93-4bb4-b33f-b72ab3d78c7c

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
theorem _root_.solution (f : Gd → ℝ) : ∑ x ∈ ({0, 1} : Finset Gd), f x = f 0 + f 1 :=
  Finset.sum_pair (by decide)
end FairSelling.TPSSefxCounterexample
