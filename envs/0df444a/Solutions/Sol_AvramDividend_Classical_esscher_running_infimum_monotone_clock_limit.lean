-- Prove2me | solution 1 for AvramDividend.Classical.esscher_running_infimum_monotone_clock_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:38:03.695986+00:00
-- url     : https://prove2.me/submissions/df5023c9-488b-4281-a4fc-211f0d9b1ed9

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set

/-- A finite, antitone running infimum converges at any horizon tending to infinity. -/
theorem solution
    (I : NNReal → ℝ)
    (hAnti : Antitone I)
    (hbdd : BddBelow (Set.range I))
    (clock : ℝ → NNReal)
    (hclock : Tendsto clock (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto (fun p : ℝ => I (clock p))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (⨅ t : NNReal, I t)) := by
  simpa only [Function.comp_def] using
    (tendsto_atTop_ciInf hAnti hbdd).comp hclock
