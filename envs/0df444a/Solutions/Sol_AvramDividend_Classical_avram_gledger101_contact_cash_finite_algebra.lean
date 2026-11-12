-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger101_contact_cash_finite_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:42:27.758246+00:00
-- url     : https://prove2.me/submissions/562357bb-8ee6-4d14-9361-73ba53d6beb2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
noncomputable section

/-- After the single crossing cell, all further contact terms vanish. -/
theorem solution
    (A : ℕ → ℝ) (N k : ℕ) (hk : k < N)
    (hafter : ∀ i : ℕ, k < i → A i = 0)
    (I U R F z cash0 term : ℝ)
    (hpre : (∑ i ∈ Finset.range k, A i) + I ≤ R)
    (hlast : A k + term ≤ 0)
    (hzero : z + cash0 ≤ 0)
    (hcash : F ≤ cash0 + I + U)
    (herr : 0 ≤ R + U) :
    max (z + (∑ i ∈ Finset.range N, A i) + term + F) 0 ≤ R + U := by
  have hN : k + 1 + (N - (k + 1)) = N := by omega
  have htail :
      (∑ i ∈ Finset.range (N - (k + 1)), A (k + 1 + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hafter (k + 1 + i) (by omega)
  have hsum : (∑ i ∈ Finset.range N, A i) =
      (∑ i ∈ Finset.range k, A i) + A k := by
    conv_lhs => rw [← hN]
    rw [Finset.sum_range_add, htail, add_zero, Finset.sum_range_succ]
  rw [hsum]
  apply max_le
  · linarith
  · exact herr
