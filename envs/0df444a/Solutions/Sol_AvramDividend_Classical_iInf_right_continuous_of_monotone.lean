-- Prove2me | solution 1 for AvramDividend.Classical.iInf_right_continuous_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:22:10.317618+00:00
-- url     : https://prove2.me/submissions/41cef0ae-df45-4bfc-886e-32c85731b4a5

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Order.CompleteLattice.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set
open scoped ENNReal


theorem solution
    {ι : Type*} [Nonempty ι]
    (F : ι → ℝ → ℝ≥0∞)
    (hmono : ∀ i, Monotone (F i))
    (hright : ∀ i x, ContinuousWithinAt (F i) (Ici x) x) :
    ∀ x : ℝ,
      ContinuousWithinAt (fun y => ⨅ i, F i y) (Ici x) x := by
  have hmonoInf : Monotone (fun y : ℝ => ⨅ i, F i y) := by
    intro a b hab
    exact iInf_mono (fun i => hmono i hab)
  intro x
  apply continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr
  constructor
  · rw [lowerSemicontinuousWithinAt_iff]
    intro y hy
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact lt_of_lt_of_le hy (hmonoInf hz)
  · apply upperSemicontinuousWithinAt_iInf
    intro i
    exact (hright i x).upperSemicontinuousWithinAt
