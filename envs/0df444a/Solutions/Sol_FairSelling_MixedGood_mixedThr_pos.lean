-- Prove2me | solution 1 for FairSelling.MixedGood.mixedThr_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:23.363637+00:00
-- url     : https://prove2.me/submissions/c49ab800-8e32-4b2a-9e47-34e1451ce23d

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
import Theorems.Thm_FairSelling_MixedGood_mixedThr_zero
import Theorems.Thm_FairSelling_MixedGood_mixedThr_one_ge

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood
namespace FairSelling.MixedGood
theorem _root_.solution (j : Fin 2) : 0 < GeneralTPS.thr mv mp j := by
  fin_cases j
  · exact lt_of_lt_of_eq (by norm_num) mixedThr_zero.symm
  · exact lt_of_lt_of_le (by norm_num) mixedThr_one_ge
end FairSelling.MixedGood
