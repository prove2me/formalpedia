-- Prove2me | solution 2 for AvramDividend.Classical.derivZeroPlus_eq_top_of_right_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:12:56.086878+00:00
-- url     : https://prove2.me/submissions/aef83894-429f-4150-bcc2-3c7c76e31c0d

import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical Filter Set
theorem solution
    (W : ℝ → ℝ)
    (hderiv : Filter.Tendsto (fun y : ℝ => deriv W y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop) :
    derivZeroPlus W = ⊤ :=
  (EReal.tendsto_coe_nhds_top_iff.2 hderiv).liminf_eq
