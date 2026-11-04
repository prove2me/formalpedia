-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_compact_derivative_implies_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:18:00.66298+00:00
-- url     : https://prove2.me/submissions/90defba7-9433-4e7f-bc64-582dc712ca20

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

/-- A uniform derivative norm on a compact reserve band controls every pairwise
increment of the original BV candidate on that band. -/
theorem solution (w : ℝ → ℝ) (a b : ℝ) (L : ℝ≥0)
  (hDiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ w x)
  (hDeriv : ∀ x ∈ Icc a b, ‖deriv w x‖₊ ≤ L) :
  ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
    |w u - w v| ≤ (L : ℝ) * |u - v| := by
  have hLip : LipschitzOnWith L w (Icc a b) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le hDiff hDeriv (convex_Icc a b)
  intro u hu v hv
  simpa only [Real.norm_eq_abs] using hLip.norm_sub_le hu hv
