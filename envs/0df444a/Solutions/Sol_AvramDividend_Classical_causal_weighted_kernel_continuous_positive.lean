-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_kernel_continuous_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:36:01.595057+00:00
-- url     : https://prove2.me/submissions/a7271334-473c-40f9-9859-9fdc81e5f5fd

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Damping an L1 kernel preserves its positive-time continuity. -/
theorem solution
    (K : ℝ → ℝ) (w β : ℝ)
    (hK : ContinuousOn K (Ioi (0 : ℝ))) :
    ContinuousOn (fun t : ℝ => Real.exp (-w * t) * (β + K t))
      (Ioi (0 : ℝ)) := by
  have hexp : Continuous (fun t : ℝ => Real.exp (-w * t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact hexp.continuousOn.mul (continuousOn_const.add hK)
