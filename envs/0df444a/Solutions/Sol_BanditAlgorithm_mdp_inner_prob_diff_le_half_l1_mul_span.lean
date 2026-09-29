-- Prove2me | solution 1 for BanditAlgorithm.mdp_inner_prob_diff_le_half_l1_mul_span
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T03:48:22.057426+00:00
-- url     : https://prove2.me/submissions/f04f9db4-77c8-4cf1-80c7-a4c3ad2e990c

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-- **The Hölder step of Eq. (38.20).**  If `P` and `Q` are probability vectors
and the value function `v` takes values in `[a, b]`, then

`⟨P - Q, v⟩ ≤ ‖P - Q‖₁ (b - a) / 2`.

The point is that only the *span* `b - a` of `v` enters, not its sup-norm: the
difference of two probability vectors is orthogonal to constants, so `v` may be
recentred at `(a+b)/2` before applying Hölder. -/
theorem solution {ι : Type*} [Fintype ι]
    (P Q v : ι → ℝ) (a b : ℝ) (hP : ∑ i, P i = 1) (hQ : ∑ i, Q i = 1)
    (hv : ∀ i, v i ∈ Set.Icc a b) :
    ∑ i, (P i - Q i) * v i ≤ (∑ i, |P i - Q i|) / 2 * (b - a) := by
  set c : ℝ := (a + b) / 2 with hc
  have hshift : ∑ i, (P i - Q i) * v i = ∑ i, (P i - Q i) * (v i - c) := by
    have : ∑ i, (P i - Q i) * (v i - c)
        = ∑ i, (P i - Q i) * v i - c * ∑ i, (P i - Q i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [this, Finset.sum_sub_distrib, hP, hQ]
    ring
  rw [hshift]
  have hbound : ∀ i, (P i - Q i) * (v i - c) ≤ |P i - Q i| * ((b - a) / 2) := by
    intro i
    obtain ⟨hva, hvb⟩ := hv i
    have habs : |v i - c| ≤ (b - a) / 2 := by
      rw [abs_le]
      constructor <;> [linarith; linarith]
    calc (P i - Q i) * (v i - c) ≤ |(P i - Q i) * (v i - c)| := le_abs_self _
      _ = |P i - Q i| * |v i - c| := abs_mul _ _
      _ ≤ |P i - Q i| * ((b - a) / 2) := by
          exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  calc ∑ i, (P i - Q i) * (v i - c)
      ≤ ∑ i, |P i - Q i| * ((b - a) / 2) := Finset.sum_le_sum fun i _ ↦ hbound i
    _ = (∑ i, |P i - Q i|) / 2 * (b - a) := by
        rw [← Finset.sum_mul]; ring
