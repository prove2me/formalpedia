-- Prove2me | solution 1 for AvramDividend.Classical.derivZeroPlus_eq_top_of_right_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:12:08.190058+00:00
-- url     : https://prove2.me/submissions/923bdb61-ae67-4a31-b92f-f76f4acf020b

import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set

/-- Divergence of the ordinary right derivative gives an infinite extended boundary derivative. -/
theorem solution
    (W : ℝ → ℝ)
    (hderiv : Tendsto (fun y : ℝ => deriv W y)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    derivZeroPlus W = ⊤ := by
  unfold derivZeroPlus
  exact (EReal.tendsto_coe_nhds_top_iff.mpr hderiv).liminf_eq
