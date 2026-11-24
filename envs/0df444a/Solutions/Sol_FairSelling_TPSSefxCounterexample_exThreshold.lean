-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:07.304653+00:00
-- url     : https://prove2.me/submissions/2b5dd437-8324-41e5-851f-4890173fbdc3

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exTPS

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution : ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp = 20 := by
  rw [exTPS]; norm_num
end FairSelling.TPSSefxCounterexample
