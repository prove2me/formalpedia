-- Prove2me | solution 1 for Csg.DiscountedCSG.shapley_contracting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:49:01.547133+00:00
-- url     : https://prove2.me/submissions/363c691c-7b81-4898-9e19-0c4623f4ca4f

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Csg_Discounted
import Theorems.Thm_Csg_DiscountedCSG_shapley_lipschitz

set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution (v u : S → ℝ) :
    dist (D.shapley v) (D.shapley u) ≤ D.l * dist v u := by
  rw [dist_pi_le_iff (mul_nonneg D.l_nonneg dist_nonneg)]
  intro s
  rw [Real.dist_eq]
  refine D.shapley_lipschitz dist_nonneg fun s' => ?_
  rw [← Real.dist_eq]
  exact dist_le_pi_dist v u s'
end Csg.DiscountedCSG
