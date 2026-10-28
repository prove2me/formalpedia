-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ofReal_antitone_iInf_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:47:02.469026+00:00
-- url     : https://prove2.me/submissions/4c44ac75-2b81-4ade-997a-662ea3f6cfe3

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

/-- The Esscher real survival-infimum limit has the canonical ENNReal value. -/
theorem solution
    (f : NNReal → ℝ) (L : ℝ)
    (hanti : Antitone f)
    (hlim : Tendsto f atTop (nhds L)) :
    (⨅ t : NNReal, ENNReal.ofReal (f t)) = ENNReal.ofReal L := by
  have hantiE :
      Antitone (fun t : NNReal => ENNReal.ofReal (f t)) := by
    intro s t hst
    exact ENNReal.ofReal_le_ofReal (hanti hst)
  have hlimE :
      Tendsto (fun t : NNReal => ENNReal.ofReal (f t))
        atTop (nhds (ENNReal.ofReal L)) :=
    (ENNReal.continuous_ofReal.tendsto L).comp hlim
  exact tendsto_nhds_unique (tendsto_atTop_iInf hantiE) hlimE
