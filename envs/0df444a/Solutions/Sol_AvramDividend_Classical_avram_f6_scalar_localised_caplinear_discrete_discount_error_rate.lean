-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_scalar_localised_caplinear_discrete_discount_error_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:06:30.822656+00:00
-- url     : https://prove2.me/submissions/a4a20f0e-8367-494c-a24d-7effa2cb6ad0

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

theorem solution
    (m : ℕ) (E V A : ℕ → ℝ) (M L : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hOsc : ∀ i < m, 0 ≤ E i - E (i + 1) ∧
      E i - E (i + 1) ≤ M)
    (hA : ∀ i < m, A i ≤ A (i + 1))
    (hCap : ∀ i < m, 0 ≤ V i ∧
      V i ≤ L * (A (i + 1) - A i)) :
    (∑ i ∈ Finset.range m, (E i - E (i + 1)) * V i) ≤
      M * L * (A m - A 0) := by
  have hterm : ∀ i ∈ Finset.range m,
      (E i - E (i + 1)) * V i ≤
        (M * L) * (A (i + 1) - A i) := by
    intro i hi
    have hOsc_i := (hOsc i (Finset.mem_range.mp hi)).2
    have hCap_i := hCap i (Finset.mem_range.mp hi)
    calc
      (E i - E (i + 1)) * V i ≤ M * V i :=
        mul_le_mul_of_nonneg_right hOsc_i hCap_i.1
      _ ≤ M * (L * (A (i + 1) - A i)) :=
        mul_le_mul_of_nonneg_left hCap_i.2 hM
      _ = (M * L) * (A (i + 1) - A i) := by ring
  have htel : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, (A (i + 1) - A i)) = A k - A 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  calc
    (∑ i ∈ Finset.range m, (E i - E (i + 1)) * V i)
      ≤ (∑ i ∈ Finset.range m,
          (M * L) * (A (i + 1) - A i)) := Finset.sum_le_sum hterm
    _ = (M * L) * (A m - A 0) := by
      rw [← Finset.mul_sum, htel]
    _ = M * L * (A m - A 0) := by ring
