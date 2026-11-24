-- Prove2me | solution 1 for FairSelling.MixedGood.mixedThr_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:53.690808+00:00
-- url     : https://prove2.me/submissions/2eb8ca09-4c01-4c88-8605-21d844d2beec

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
import Theorems.Thm_FairSelling_MixedGood_mixedTPS_zero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood
namespace FairSelling.MixedGood
theorem _root_.solution : GeneralTPS.thr mv mp 0 = 4 / 3 := by
  unfold GeneralTPS.thr
  rw [mixedTPS_zero]
  norm_num
end FairSelling.MixedGood
