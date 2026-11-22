-- Prove2me | solution 1 for Csg.DiscountedCSG.contractingWith_shapley
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:27:14.524334+00:00
-- url     : https://prove2.me/submissions/0edecf3d-48be-41a0-900f-dd4acbac78bd

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Csg_Discounted
import Theorems.Thm_Csg_DiscountedCSG_lipschitzWith_shapley

set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution : ContractingWith D.lNN D.shapley :=
  ⟨by exact_mod_cast D.l_lt_one, D.lipschitzWith_shapley⟩
end Csg.DiscountedCSG
