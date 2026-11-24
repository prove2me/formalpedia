-- Prove2me | solution 1 for FairSelling.MixedGood.mixedThr_one_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:39.491796+00:00
-- url     : https://prove2.me/submissions/1890acd5-c06e-44d4-9798-5f4ba80b964c

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
import Theorems.Thm_FairSelling_MixedGood_mixedTPS_one_ge

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood
namespace FairSelling.MixedGood
theorem _root_.solution : (8 : ℝ) ≤ GeneralTPS.thr mv mp 1 := by
  unfold GeneralTPS.thr
  have := mixedTPS_one_ge
  norm_num
  linarith
end FairSelling.MixedGood
