-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_continuous_test_small_left_cutoff_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:43:19.332387+00:00
-- url     : https://prove2.me/submissions/2385455d-0b5d-4fc3-8dfc-fa9aabcab345

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Topology

/-- A continuous test vanishing at its negative support boundary is uniformly
small in a one-sided strip to the left; the strip can avoid cutoff atoms. -/
theorem solution (f : ℝ → ℝ) (ρ ε : ℝ) (hε : 0 < ε)
    (hfcont : ContinuousAt f (-ρ)) (hfzero : f (-ρ) = 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℝ, -ρ - δ < z → z ≤ -ρ → |f z| < ε := by
  obtain ⟨δ, hδ, hbound⟩ :=
    (Metric.continuousAt_iff.mp hfcont) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z hz hle
  have hdist : dist z (-ρ) < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  simpa only [hfzero, Real.dist_eq, sub_zero] using hbound hdist
