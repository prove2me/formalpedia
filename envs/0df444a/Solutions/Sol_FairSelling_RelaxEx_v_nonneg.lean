-- Prove2me | solution 1 for FairSelling.RelaxEx.v_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:34.119657+00:00
-- url     : https://prove2.me/submissions/26a6271f-0865-46b5-b365-3793cdbb0f15

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.RelaxEx
namespace FairSelling.RelaxEx
theorem _root_.solution : ∀ i g, 0 ≤ v i g := by
  intro i g; fin_cases i <;> fin_cases g <;> norm_num [v]
end FairSelling.RelaxEx
