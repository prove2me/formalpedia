-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:07:17.321315+00:00
-- url     : https://prove2.me/submissions/c83911d2-516e-4841-91cf-ca0de25754a4

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal
noncomputable section
/-- Original first-contact horizon prevents earlier band incursions. -/
theorem solution
    (f : ℝ≥0 → ℝ) (b : ℝ) (T : ℝ≥0)
    (hFirst : sInf ((Icc (0 : ℝ≥0) T ∩ (fun t : ℝ≥0 => -(f t)) ⁻¹' Ici (-b)) ∪ {T}) = T) :
    ∀ t : ℝ≥0, t < T → b < f t := by
  intro t ht
  by_contra h
  have hfb : f t ≤ b := le_of_not_gt h
  have hmem : t ∈ ((Icc (0 : ℝ≥0) T ∩ (fun t : ℝ≥0 => -(f t)) ⁻¹' Ici (-b)) ∪ {T}) := by
    left
    refine ⟨⟨bot_le, le_of_lt ht⟩, ?_⟩
    change -b ≤ -(f t)
    exact neg_le_neg hfb
  have hle : T ≤ t := by
    rw [← hFirst]
    exact csInf_le' hmem
  exact (not_le_of_gt ht) hle
