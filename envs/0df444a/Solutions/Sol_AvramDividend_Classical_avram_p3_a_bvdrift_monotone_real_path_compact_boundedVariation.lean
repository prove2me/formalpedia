-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_monotone_real_path_compact_boundedVariation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:14:53.041229+00:00
-- url     : https://prove2.me/submissions/99f644fa-509e-4149-95d9-d7950ecaa19b

import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UniformSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

/-- Every nondecreasing real path on nonnegative time has bounded
total variation on every bounded interval, with explicit endpoint bounds. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hm : Monotone f) (a b : ℝ≥0) (hab : a ≤ b) :
    BoundedVariationOn f (Icc a b) := by
  apply MonotoneOn.boundedVariationOn
    (s := Icc a b) (C := max (|f a|) (|f b|))
  · intro x hx y hy hxy
    exact hm hxy
  · intro x hx
    have hax : f a ≤ f x := hm hx.1
    have hxb : f x ≤ f b := hm hx.2
    apply abs_le.mpr
    constructor
    · exact (neg_le_neg (le_max_left (|f a|) (|f b|))).trans
        ((neg_abs_le (f a)).trans hax)
    · exact hxb.trans ((le_abs_self (f b)).trans
        (le_max_right (|f a|) (|f b|)))
