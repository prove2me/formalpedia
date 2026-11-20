-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_nonuniform_clipped_discounted_generator_mesh_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:04:36.304431+00:00
-- url     : https://prove2.me/submissions/c9f120c9-df60-4023-8684-ca83be96777a

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Ring
open MeasureTheory Set
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    (m : ℕ) (v : ℕ → ℝ)
    (hv : Monotone v) (hv0 : v 0 = 0)
    (T : ℝ) (hT : v m ≤ T)
    (B : ℝ) (hB : 0 ≤ B)
    (E F : ℕ → ℝ)
    (hE : ∀ i < m, 0 ≤ E i ∧ E i ≤ 1)
    (hF : ∀ i < m, |F i| ≤ B) :
    |∑ i ∈ Finset.range m,
      E i * (v (i + 1) - v i) * F i| ≤ T * B := by
  have hstep : ∀ i, 0 ≤ v (i + 1) - v i := by
    intro i
    exact sub_nonneg.mpr (hv (Nat.le_succ i))
  have htel : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, (v (i + 1) - v i)) = v k - v 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hterm : ∀ i < m,
      |E i * (v (i + 1) - v i) * F i| ≤
        (v (i + 1) - v i) * B := by
    intro i hi
    rcases hE i hi with ⟨he0, he1⟩
    have hEabs : E i * |F i| ≤ B := by
      calc
        E i * |F i| ≤ 1 * |F i| :=
          mul_le_mul_of_nonneg_right he1 (abs_nonneg _)
        _ = |F i| := one_mul _
        _ ≤ B := hF i hi
    rw [abs_mul, abs_mul, abs_of_nonneg he0,
      abs_of_nonneg (hstep i)]
    calc
      E i * (v (i + 1) - v i) * |F i| =
          (v (i + 1) - v i) * (E i * |F i|) := by ring
      _ ≤ (v (i + 1) - v i) * B :=
          mul_le_mul_of_nonneg_left hEabs (hstep i)
  calc
    |∑ i ∈ Finset.range m,
      E i * (v (i + 1) - v i) * F i| ≤
      ∑ i ∈ Finset.range m,
        |E i * (v (i + 1) - v i) * F i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range m,
        (v (i + 1) - v i) * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i (Finset.mem_range.mp hi)
    _ = (v m - v 0) * B := by
      rw [← Finset.sum_mul, htel m]
    _ = v m * B := by rw [hv0]; ring
    _ ≤ T * B := mul_le_mul_of_nonneg_right hT hB