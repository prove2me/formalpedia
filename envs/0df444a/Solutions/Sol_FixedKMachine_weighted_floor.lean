-- Prove2me | solution 1 for FixedKMachine.weighted_floor
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:02:50.172773+00:00
-- url     : https://prove2.me/submissions/cd326542-f46d-46df-af79-ab9907d62f74

import Mathlib
open MeasureTheory Set

theorem solution (w g : ℕ → ℝ) (s : Finset ℕ) (m : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hfloor : ∀ i ∈ s, m ≤ g i)
    (hsum : ∑ i ∈ s, w i = 1) : m ≤ ∑ i ∈ s, w i*g i := by
  calc
    m = (∑ i ∈ s, w i)*m := by rw [hsum]; ring
    _ = ∑ i ∈ s, w i*m := Finset.sum_mul s w m
    _ ≤ ∑ i ∈ s, w i*g i := Finset.sum_le_sum (by
      intro i hi
      exact mul_le_mul_of_nonneg_left (hfloor i hi) (hw i hi))
