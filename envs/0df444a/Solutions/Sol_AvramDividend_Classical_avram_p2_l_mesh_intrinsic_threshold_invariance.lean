-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_intrinsic_threshold_invariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:34:12.031206+00:00
-- url     : https://prove2.me/submissions/d234eaf5-2650-485c-958c-31ec7da1a02c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal BigOperators Classical

/-- The finite intrinsic marked-test sum is independent of the auxiliary
large-jump threshold once that threshold is below the test's negative support. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (ρ σ : ℝ) (hρσ : ρ ≤ σ)
    (f : ℝ → ℝ) (hf : ∀ z : ℝ, -σ < z → f z = 0)
    (Sρ Sσ : Finset ℝ≥0)
    (hSρ : ∀ u : ℝ≥0,
      u ∈ Sρ ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|)
    (hSσ : ∀ u : ℝ≥0,
      u ∈ Sσ ↔ 0 < u ∧ u ≤ T ∧
        σ ≤ |Y u - Function.leftLim Y u|) :
    (∑ u ∈ Sρ, f (Y u - Function.leftLim Y u)) =
      ∑ u ∈ Sσ, f (Y u - Function.leftLim Y u) := by
  classical
  have hsub : Sσ ⊆ Sρ := by
    intro u hu
    obtain ⟨hu0, huT, huσ⟩ := (hSσ u).mp hu
    exact (hSρ u).mpr ⟨hu0, huT, le_trans hρσ huσ⟩
  symm
  apply Finset.sum_subset hsub
  intro u huρ huσ
  obtain ⟨hu0, huT, _⟩ := (hSρ u).mp huρ
  have hsmall : |Y u - Function.leftLim Y u| < σ := by
    by_contra hn
    have hlarge : σ ≤ |Y u - Function.leftLim Y u| := le_of_not_gt hn
    exact huσ ((hSσ u).mpr ⟨hu0, huT, hlarge⟩)
  apply hf
  have hle := neg_abs_le (Y u - Function.leftLim Y u)
  linarith
