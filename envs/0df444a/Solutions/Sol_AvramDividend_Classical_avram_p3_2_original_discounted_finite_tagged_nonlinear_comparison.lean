-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_discounted_finite_tagged_nonlinear_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:45:54.604385+00:00
-- url     : https://prove2.me/submissions/129c4bd1-1369-4c07-87c9-45cdccb27a6e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

/-- Exact weighted finite-grid comparison with a second jump-time discount:
the physical BV cell residual and the time-discount mismatch are separated. -/
theorem solution
    (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ, |w x - w y| ≤ L * |x - y|)
    (n : ℕ) (e d z p j a : Fin n → ℝ)
    (he : ∀ i, 0 ≤ e i) :
    |(∑ i : Fin n, e i * (w (z i - j i) - w (z i))) -
      (∑ i : Fin n, d i * (w (p i - a i) - w (p i)))| ≤
      (∑ i : Fin n, e i *
        (L * |j i - a i| + 2 * L * |z i - p i|)) +
      (∑ i : Fin n, |e i - d i| *
        |w (p i - a i) - w (p i)|) := by
  classical
  let F : Fin n → ℝ := fun i =>
    e i * (w (z i - j i) - w (z i)) -
      d i * (w (p i - a i) - w (p i))
  let B : Fin n → ℝ := fun i =>
    e i * (L * |j i - a i| + 2 * L * |z i - p i|) +
      |e i - d i| * |w (p i - a i) - w (p i)|
  have hTerm (i : Fin n) : |(w (z i - j i) - w (z i)) -
      (w (p i - a i) - w (p i))| ≤ L * |j i - a i| + 2 * L * |z i - p i| := by
    have h1 := hLip (z i - j i) (z i - a i)
    have h2 := hLip (z i - a i) (p i - a i)
    have h3 := hLip (p i) (z i)
    have hd1 : (z i - j i) - (z i - a i) = -(j i - a i) := by ring
    have hd2 : (z i - a i) - (p i - a i) = z i - p i := by ring
    have hd3 : p i - z i = -(z i - p i) := by ring
    rw [hd1, abs_neg] at h1
    rw [hd2] at h2
    rw [hd3, abs_neg] at h3
    have hid :
        (w (z i - j i) - w (z i)) -
          (w (p i - a i) - w (p i)) =
        ((w (z i - j i) - w (z i - a i)) +
          (w (z i - a i) - w (p i - a i))) +
          (w (p i) - w (z i)) := by ring
    rw [hid]
    have ha := abs_add_le (w (z i - j i) - w (z i - a i) +
      (w (z i - a i) - w (p i - a i))) (w (p i) - w (z i))
    have hb := abs_add_le (w (z i - j i) - w (z i - a i))
      (w (z i - a i) - w (p i - a i))
    linarith only [ha, hb, h1, h2, h3]
  have hCell (i : Fin n) : |F i| ≤ B i := by
    dsimp [F, B]
    have hEq : e i * (w (z i - j i) - w (z i)) -
        d i * (w (p i - a i) - w (p i)) =
        e i * ((w (z i - j i) - w (z i)) - (w (p i - a i) - w (p i))) +
        (e i - d i) * (w (p i - a i) - w (p i)) := by ring
    rw [hEq]
    calc
      _ ≤ |e i * ((w (z i - j i) - w (z i)) -
              (w (p i - a i) - w (p i)))| +
          |(e i - d i) * (w (p i - a i) - w (p i))| :=
            abs_add_le _ _
      _ = e i * |(w (z i - j i) - w (z i)) -
              (w (p i - a i) - w (p i))| +
          |e i - d i| * |w (p i - a i) - w (p i)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (he i)]
      _ ≤ e i * (L * |j i - a i| + 2 * L * |z i - p i|) +
          |e i - d i| * |w (p i - a i) - w (p i)| := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hTerm i) (he i)) le_rfl
  have hAll (s : Finset (Fin n)) :
      |∑ i ∈ s, F i| ≤ ∑ i ∈ s, B i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc
        |F i + ∑ j ∈ s, F j| ≤
            |F i| + |∑ j ∈ s, F j| := abs_add_le _ _
        _ ≤ B i + ∑ j ∈ s, B j := add_le_add (hCell i) ih
  have h := hAll Finset.univ
  simpa only [F, B, Finset.sum_sub_distrib, Finset.sum_add_distrib] using h
