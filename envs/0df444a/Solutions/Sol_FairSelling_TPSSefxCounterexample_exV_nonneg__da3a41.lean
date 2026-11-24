-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:11.143192+00:00
-- url     : https://prove2.me/submissions/cf56ae7b-7e46-46b4-85c7-f513ad485223

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution : ∀ i g, 0 ≤ exV i g := fun _ => exv_nonneg
end FairSelling.TPSSefxCounterexample
