-- Prove2me | solution 1 for EdenVerified.p16_exp_fifth_lt_planar_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:26:44.110169+00:00
-- url     : https://prove2.me/submissions/722a5d26-1fbb-407c-8c15-bed0e3d0033c

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_exp_fifth_lt_planar_bound


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    Real.exp (-c * t) < Real.exp (-4 * t) :=
  @Eden.exp_fifth_lt_planar_bound
end EdenVerified
