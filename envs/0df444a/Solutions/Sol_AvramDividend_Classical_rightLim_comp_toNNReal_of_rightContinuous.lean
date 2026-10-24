-- Prove2me | solution 1 for AvramDividend.Classical.rightLim_comp_toNNReal_of_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:18:13.379029+00:00
-- url     : https://prove2.me/submissions/7beccf96-b8ec-489e-8cd0-235549827dbb

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Instances.NNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology
open scoped NNReal

/-- A right-continuous nonnegative-time path has the expected lifted real-time right limits. -/
theorem solution
    (f : ℝ≥0 → ℝ)
    (hf : ∀ s : ℝ≥0, ContinuousWithinAt f (Set.Ici s) s)
    (r : ℝ) :
    Function.rightLim (fun s : ℝ => f s.toNNReal) r = f r.toNNReal := by
  have hc : ContinuousWithinAt Real.toNNReal (Set.Ici r) r :=
    continuous_real_toNNReal.continuousWithinAt
  have hm : Set.MapsTo Real.toNNReal (Set.Ici r) (Set.Ici r.toNNReal) := by
    intro s hs
    exact Real.toNNReal_mono hs
  have hcomp :
      ContinuousWithinAt (fun s : ℝ => f s.toNNReal) (Set.Ici r) r := by
    change ContinuousWithinAt (f ∘ Real.toNNReal) (Set.Ici r) r
    exact (hf r.toNNReal).comp hc hm
  exact hcomp.rightLim_eq
