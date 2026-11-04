-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_strict_negative_tsupport_gives_zero_near_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:48:33.839417+00:00
-- url     : https://prove2.me/submissions/9a1f75e9-80a0-447a-bbe7-0a8c6d5c9b47

import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology

/-- A test whose closed topological support is strictly negative
vanishes on an actual neighbourhood of the origin. -/
theorem solution (f : ℝ → ℝ)
    (hneg : tsupport f ⊆ Set.Iio (0 : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ, |z| < ρ → f z = 0 := by
  have h0 : (0 : ℝ) ∉ tsupport f := by
    intro hz
    exact (lt_irrefl (0 : ℝ)) (hneg hz)
  obtain ⟨ρ, hρ, hball⟩ :=
    (Metric.isOpen_iff.mp (isClosed_tsupport f).isOpen_compl) 0 h0
  refine ⟨ρ, hρ, ?_⟩
  intro z hz
  apply image_eq_zero_of_notMem_tsupport
  apply hball
  simpa [Metric.mem_ball, Real.dist_eq] using hz
