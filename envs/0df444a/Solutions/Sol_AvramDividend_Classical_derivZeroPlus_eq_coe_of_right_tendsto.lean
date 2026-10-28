-- Prove2me | solution 1 for AvramDividend.Classical.derivZeroPlus_eq_coe_of_right_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:08:23.845091+00:00
-- url     : https://prove2.me/submissions/3c5ecf6c-8348-4796-9e0f-4e5f62642219

import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set

/-- The extended right-derivative liminf equals any finite genuine right derivative limit. -/
theorem solution
    (W : ℝ → ℝ) (d : ℝ)
    (hderiv : Tendsto (fun y : ℝ => deriv W y)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds d)) :
    derivZeroPlus W = (d : EReal) := by
  unfold derivZeroPlus
  exact (EReal.tendsto_coe.mpr hderiv).liminf_eq
