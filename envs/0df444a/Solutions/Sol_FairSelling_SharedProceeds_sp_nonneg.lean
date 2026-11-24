-- Prove2me | solution 1 for FairSelling.SharedProceeds.sp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:38.66852+00:00
-- url     : https://prove2.me/submissions/ddb48eed-f3b2-42ba-822d-dbcdb7bb4123

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds
namespace FairSelling.SharedProceeds
theorem _root_.solution : ∀ g, 0 ≤ sp g := by
  intro g; fin_cases g <;> norm_num [sp]
end FairSelling.SharedProceeds
