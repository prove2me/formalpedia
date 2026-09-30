-- Prove2me | solution 1 for ComputationalLearning.phi_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:34:11.745965+00:00
-- url     : https://prove2.me/submissions/940153e2-c98f-4bc9-8c36-bc5e70cf1e3b

import Mathlib
import Definitions.Def_ComputationalLearning_VC

open MeasureTheory

namespace ComputationalLearning

lemma phi_closed (d m : ℕ) : Phi d m = ∑ i ∈ Finset.range (d + 1), m.choose i := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero => simp [Phi]
    | succ d => simp [Phi, Finset.sum_range_succ']
  | succ m ih =>
    cases d with
    | zero => simp [Phi]
    | succ d =>
      rw [show Phi (d + 1) (m + 1) = Phi (d + 1) m + Phi d m from rfl, ih (d + 1), ih d]
      rw [Finset.sum_range_succ' (fun i => (m + 1).choose i),
        Finset.sum_range_succ' (fun i => m.choose i) (d + 1)]
      simp only [Nat.choose_succ_succ, Finset.sum_add_distrib, Nat.choose_zero_right]
      ring

theorem phi_main (d m : ℕ) :
    (m ≤ d → Phi d m = 2 ^ m) ∧
    (1 ≤ d → d ≤ m → (Phi d m : ℝ) ≤ (Real.exp 1 * m / d) ^ d) := by
  constructor
  · intro hmd
    rw [phi_closed, ← Nat.sum_range_choose m]
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro i hi hnot
    simp only [Finset.mem_range] at hi hnot
    exact Nat.choose_eq_zero_of_lt (by omega)
  · intro hd hdm
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hmR : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hd hdm)
    have hdm' : (d:ℝ) ≤ m := by exact_mod_cast hdm
    set r : ℝ := d / m with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 := by rw [hr, div_le_one hmR]; exact hdm'
    have hrd : 0 < r ^ d := pow_pos hr0 d
    rw [phi_closed]
    push_cast
    have step1 : ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) ≤
        (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * r ^ i) / r ^ d := by
      rw [le_div_iff₀ hrd, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.mem_range] at hi
      have : r ^ d ≤ r ^ i := pow_le_pow_of_le_one hr0.le hr1 (by omega)
      exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    have step2 : ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * r ^ i ≤
        ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * r ^ i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      intro i _ _
      positivity
    have step3 : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * r ^ i = (r + 1) ^ m := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro i _
      rw [one_pow, mul_one, mul_comm]
    have step4 : (r + 1) ^ m ≤ Real.exp d := by
      calc (r + 1) ^ m ≤ (Real.exp r) ^ m :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) m
        _ = Real.exp (m * r) := by rw [← Real.exp_nat_mul]
        _ = Real.exp d := by rw [hr]; congr 1; field_simp
    have step5 : Real.exp d / r ^ d = (Real.exp 1 * m / d) ^ d := by
      rw [show Real.exp d = Real.exp 1 ^ d by rw [← Real.exp_nat_mul, mul_one], hr, div_pow,
        mul_div_assoc, mul_pow, div_pow]
      field_simp
    calc ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ)
        ≤ (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * r ^ i) / r ^ d := step1
      _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * r ^ i) / r ^ d :=
          div_le_div_of_nonneg_right step2 hrd.le
      _ = (r + 1) ^ m / r ^ d := by rw [step3]
      _ ≤ Real.exp d / r ^ d := div_le_div_of_nonneg_right step4 hrd.le
      _ = (Real.exp 1 * m / d) ^ d := step5

end ComputationalLearning

open ComputationalLearning

theorem solution (d m : ℕ) :
    (m ≤ d → Phi d m = 2 ^ m) ∧
    (1 ≤ d → d ≤ m → (Phi d m : ℝ) ≤ (Real.exp 1 * m / d) ^ d) := by
  exact phi_main d m
