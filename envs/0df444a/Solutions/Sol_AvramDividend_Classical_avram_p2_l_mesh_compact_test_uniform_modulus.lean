-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_compact_test_uniform_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:48:07.498094+00:00
-- url     : https://prove2.me/submissions/1a74bbd7-b022-4deb-857d-02f560c8070e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Topology

/-- A compactly supported continuous real jump test has one global
modulus of continuity, usable across every cell of a finite partition. -/
theorem solution (f : ℝ → ℝ)
    (hfcomp : HasCompactSupport f) (hfcont : Continuous f)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : ℝ, |x - y| < δ → |f x - f y| < η := by
  have hunif : UniformContinuous f :=
    hfcomp.uniformContinuous_of_continuous hfcont
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuous_iff.mp hunif) η hη
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hdist : dist x y < δ := by
    simpa only [Real.dist_eq] using hxy
  simpa only [Real.dist_eq] using (hmod hdist)
