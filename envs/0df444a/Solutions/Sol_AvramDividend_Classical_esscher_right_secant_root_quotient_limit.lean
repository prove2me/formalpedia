-- Prove2me | solution 1 for AvramDividend.Classical.esscher_right_secant_root_quotient_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T20:03:13.163014+00:00
-- url     : https://prove2.me/submissions/b9abe5c5-e779-4a7e-a5dd-a141f6e4dda8

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Order.Field
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set

/-- Right secant convergence, not two-sided differentiability, controls
    the genuine positive-level root quotient. -/
theorem solution
    (f : ℝ → ℝ) (φ m : ℝ) (root : ℝ → ℝ)
    (hroot : ∀ p : ℝ, 0 < p →
      f (φ + root p) - f φ = p)
    (hrootLim : Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hsec : Tendsto (fun h : ℝ => (f (φ + h) - f φ) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m)) :
    Tendsto (fun p : ℝ => p / root p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) := by
  have hEq :
      (fun p : ℝ => (f (φ + root p) - f φ) / root p) =ᶠ[
        nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun p : ℝ => p / root p) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    rw [hroot p hp]
  exact (hsec.comp hrootLim).congr' hEq
