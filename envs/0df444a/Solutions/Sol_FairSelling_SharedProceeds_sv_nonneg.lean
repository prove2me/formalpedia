-- Prove2me | solution 1 for FairSelling.SharedProceeds.sv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:39.213699+00:00
-- url     : https://prove2.me/submissions/e38d1c65-f231-4a94-a9ce-7152f19ec4d1

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds
namespace FairSelling.SharedProceeds
theorem _root_.solution : ∀ g, 0 ≤ sv g := by
  intro g; fin_cases g <;> norm_num [sv, Fin.ext_iff]
end FairSelling.SharedProceeds
