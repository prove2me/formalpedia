-- Prove2me | solution 1 for Csg.DiscountedCSG.lipschitzWith_shapley
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:25:31.696806+00:00
-- url     : https://prove2.me/submissions/8c129985-1ea8-4700-bb02-14d6909bf8fc

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Csg_Discounted
import Theorems.Thm_Csg_DiscountedCSG_shapley_contracting

set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution : LipschitzWith D.lNN D.shapley :=
  LipschitzWith.of_dist_le_mul fun v u => D.shapley_contracting v u
end Csg.DiscountedCSG
