-- Prove2me | solution 1 for Csg.DiscountedCSG.exists_unique_fixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:29:21.707155+00:00
-- url     : https://prove2.me/submissions/6e345de4-1841-4d81-a257-2fc1389866bc

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Csg_Discounted
import Theorems.Thm_Csg_DiscountedCSG_shapley_contracting
import Theorems.Thm_Csg_DiscountedCSG_contractingWith_shapley

set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution : ∃! v : S → ℝ, D.shapley v = v := by
  obtain ⟨v, hv_fix, -, -⟩ := D.contractingWith_shapley.exists_fixedPoint 0 (edist_ne_top _ _)
  refine ⟨v, hv_fix, fun w hw_fix => ?_⟩
  by_contra hne
  have hpos : 0 < dist v w := dist_pos.mpr (Ne.symm hne)
  have hshrink : dist v w ≤ D.l * dist v w := by
    have := D.shapley_contracting v w
    rwa [hv_fix, hw_fix] at this
  nlinarith [D.l_lt_one]
end Csg.DiscountedCSG
