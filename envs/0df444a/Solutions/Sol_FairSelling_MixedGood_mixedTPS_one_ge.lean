-- Prove2me | solution 1 for FairSelling.MixedGood.mixedTPS_one_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:42.592207+00:00
-- url     : https://prove2.me/submissions/0980a127-c954-4010-b2eb-becb264862cd

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
import Theorems.Thm_FairSelling_le_TPS_of_le_truncSum


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood
namespace FairSelling.MixedGood
theorem _root_.solution : (12 : ℝ) ≤ TPS 2 (mv 1) mp := by
  refine le_TPS_of_le_truncSum (mv 1) mp ?_
  unfold truncSum
  rw [Fin.sum_univ_three]
  rw [show mp 0 = 4 from rfl, show mp 1 = 0 from rfl, show mp 2 = 0 from rfl,
    show mv 1 0 = 100 from rfl, show mv 1 1 = 6 from rfl, show mv 1 2 = 6 from rfl]
  norm_num
end FairSelling.MixedGood
