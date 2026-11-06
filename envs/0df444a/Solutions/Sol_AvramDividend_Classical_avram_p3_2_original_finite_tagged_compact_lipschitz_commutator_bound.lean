-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_finite_tagged_compact_lipschitz_commutator_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:35:06.62505+00:00
-- url     : https://prove2.me/submissions/952daf44-e81e-4a3d-90ac-5c059bfc6014

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

/-- A compact-band Lipschitz estimate controls finite original physical jump
commutators whenever both pre- and post-jump reserve states remain in-band. -/
theorem solution
    (w : ℝ → ℝ) (lo hi L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      |w x - w y| ≤ L * |x - y|)
    (n : ℕ) (e z p j a : Fin n → ℝ)
    (he : ∀ i, 0 ≤ e i)
    (hPoints : ∀ i,
      z i ∈ Set.Icc lo hi ∧ z i - j i ∈ Set.Icc lo hi ∧
      p i ∈ Set.Icc lo hi ∧ p i - a i ∈ Set.Icc lo hi) :
    |∑ i : Fin n, e i *
      ((w (z i - j i) - w (z i)) -
        (w (p i - a i) - w (p i)))| ≤
      ∑ i : Fin n, e i *
        (L * |j i - a i| + 2 * L * |z i - p i|) := by
  have hcell (i : Fin n) :
      |(w (z i - j i) - w (z i)) -
          (w (p i - a i) - w (p i))| ≤
        L * |j i - a i| + 2 * L * |z i - p i| := by
    have hfirst := hLip (z i - j i) (hPoints i).2.1
      (p i - a i) (hPoints i).2.2.2
    have hsecond := hLip (z i) (hPoints i).1
      (p i) (hPoints i).2.2.1
    have htriangle :
        |(z i - j i) - (p i - a i)| ≤
          |z i - p i| + |j i - a i| := by
      calc
        |(z i - j i) - (p i - a i)| =
            |(z i - p i) - (j i - a i)| := by congr 1; ring
        _ ≤ |z i - p i| + |j i - a i| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (z i - p i) (0 : ℝ) (j i - a i))
    calc
      |(w (z i - j i) - w (z i)) -
          (w (p i - a i) - w (p i))| =
          |(w (z i - j i) - w (p i - a i)) -
            (w (z i) - w (p i))| := by congr 1; ring
      _ ≤ |w (z i - j i) - w (p i - a i)| +
          |w (z i) - w (p i)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (w (z i - j i) - w (p i - a i))
            (0 : ℝ) (w (z i) - w (p i)))
      _ ≤ L * |(z i - j i) - (p i - a i)| +
          L * |z i - p i| := add_le_add hfirst hsecond
      _ ≤ L * (|z i - p i| + |j i - a i|) +
          L * |z i - p i| :=
        add_le_add (mul_le_mul_of_nonneg_left htriangle hL) le_rfl
      _ = L * |j i - a i| + 2 * L * |z i - p i| := by ring
  calc
    |∑ i : Fin n, e i *
        ((w (z i - j i) - w (z i)) -
          (w (p i - a i) - w (p i)))| ≤
      ∑ i : Fin n, |e i *
        ((w (z i - j i) - w (z i)) -
          (w (p i - a i) - w (p i)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, e i *
        |(w (z i - j i) - w (z i)) -
          (w (p i - a i) - w (p i))| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (he i)]
    _ ≤ ∑ i : Fin n, e i *
        (L * |j i - a i| + 2 * L * |z i - p i|) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hcell i) (he i)
