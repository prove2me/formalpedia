-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_intrinsic_finite_test_difference_stability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:02:36.382488+00:00
-- url     : https://prove2.me/submissions/70da20df-28c0-4dd5-9dea-9934e4e682a4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal BigOperators Classical

/-- Uniform test approximation controls the finite intrinsic marked-jump
sum without imposing continuity or a boundary-atom condition. -/
theorem solution (Y : ℝ≥0 → ℝ) (S : Finset ℝ≥0)
    (f g : ℝ → ℝ) (δ : ℝ)
    (hδ : ∀ z : ℝ, |f z - g z| ≤ δ) :
    |(∑ u ∈ S, f (Y u - Function.leftLim Y u)) -
      (∑ u ∈ S, g (Y u - Function.leftLim Y u))| ≤
        (S.card : ℝ) * δ := by
  classical
  have hfin (s : Finset ℝ≥0) :
      |∑ u ∈ s, (f (Y u - Function.leftLim Y u) -
        g (Y u - Function.leftLim Y u))| ≤ (s.card : ℝ) * δ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      calc
        |∑ u ∈ insert a s, (f (Y u - Function.leftLim Y u) -
          g (Y u - Function.leftLim Y u))| =
            |(f (Y a - Function.leftLim Y a) -
              g (Y a - Function.leftLim Y a)) +
              ∑ u ∈ s, (f (Y u - Function.leftLim Y u) -
                g (Y u - Function.leftLim Y u))| := by
                  rw [Finset.sum_insert ha]
        _ ≤ |f (Y a - Function.leftLim Y a) -
              g (Y a - Function.leftLim Y a)| +
              |∑ u ∈ s, (f (Y u - Function.leftLim Y u) -
                g (Y u - Function.leftLim Y u))| := abs_add_le _ _
        _ ≤ δ + (s.card : ℝ) * δ := add_le_add (hδ _) ih
        _ = ((insert a s).card : ℝ) * δ := by
          simp [ha]
          ring
  simpa only [Finset.sum_sub_distrib] using hfin S
