-- Prove2me | solution 1 for GamblersFallacy.proposition_2_last_inequality
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:44:35.532674+00:00
-- url     : https://prove2.me/submissions/c8f609b5-a8fb-4a41-a65c-5146008d5df4

import Mathlib
namespace GamblersFallacy

theorem proposition_2_last_inequality (m : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    1 ≤ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) * (((m : ℝ) * p + 2) / ((i : ℝ) + 2)) ∧
      (1 ≤ m → 1 < ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) * (((m : ℝ) * p + 2) / ((i : ℝ) + 2))) := by
  obtain ⟨hp0, hp1⟩ := hp
  set w : ℕ → ℝ := fun i => (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) with hw
  set c : ℝ := (m : ℝ) * p + 2 with hc
  have c0 : 0 < c := by positivity
  have w0 : ∀ i, 0 ≤ w i := fun i => by
    have : 0 ≤ 1 - p := by linarith
    positivity
  have hsum1 : ∑ i ∈ Finset.range (m + 1), w i = 1 := by
    have := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum ℝ m)
    rw [Polynomial.eval_finset_sum, Polynomial.eval_one] at this
    rw [← this]
    apply Finset.sum_congr rfl; intro i _
    simp [bernsteinPolynomial, hw]
  have hsumi : ∑ i ∈ Finset.range (m + 1), w i * i = m * p := by
    have := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum_smul ℝ m)
    rw [Polynomial.eval_finset_sum, Polynomial.eval_smul, Polynomial.eval_X] at this
    rw [nsmul_eq_mul] at this
    rw [← this]
    apply Finset.sum_congr rfl; intro i _
    simp [bernsteinPolynomial, hw, nsmul_eq_mul]; ring
  have hlow : ∀ i : ℕ, w i * (2 - ((i : ℝ) + 2) / c) ≤ w i * (c / ((i : ℝ) + 2)) := by
    intro i
    apply mul_le_mul_of_nonneg_left _ (w0 i)
    have ha : 0 < (i : ℝ) + 2 := by positivity
    have key : 2 - ((i : ℝ) + 2) / c - c / ((i : ℝ) + 2) = -((c - ((i : ℝ) + 2)) ^ 2 / (c * ((i : ℝ) + 2))) := by
      field_simp; ring
    have : 0 ≤ (c - ((i : ℝ) + 2)) ^ 2 / (c * ((i : ℝ) + 2)) := by positivity
    linarith
  have hbase : ∑ i ∈ Finset.range (m + 1), w i * (2 - ((i : ℝ) + 2) / c) = 1 := by
    have e : ∀ i : ℕ, w i * (2 - ((i : ℝ) + 2) / c) = 2 * w i - (w i * i + 2 * w i) / c := by
      intro i; field_simp; try ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsum1, hsumi]
    rw [show (m : ℝ) * p + 2 * 1 = c by rw [hc]; ring, div_self c0.ne']
    ring
  have hS : ∀ i, (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) * (((m : ℝ) * p + 2) / ((i : ℝ) + 2))
      = w i * (c / ((i : ℝ) + 2)) := fun i => rfl
  constructor
  · have h := Finset.sum_le_sum (s := Finset.range (m + 1)) (fun i _ => hlow i)
    rw [hbase] at h; exact h
  · intro hm
    suffices h : ∑ i ∈ Finset.range (m + 1), w i * (2 - ((i : ℝ) + 2) / c) <
        ∑ i ∈ Finset.range (m + 1), w i * (c / ((i : ℝ) + 2)) by
      rw [hbase] at h; exact h
    apply Finset.sum_lt_sum (fun i _ => hlow i)
    refine ⟨0, by simp, ?_⟩
    have hw0 : 0 < w 0 := by simp [hw]; exact pow_pos (by linarith) _
    apply mul_lt_mul_of_pos_left _ hw0
    have hc2 : 2 < c := by
      have : (0 : ℝ) < m * p := mul_pos (by exact_mod_cast hm) hp0
      linarith
    push_cast
    have key : c / (0 + 2) - (2 - (0 + 2) / c) = (c - 2) ^ 2 / (2 * c) := by
      field_simp; ring
    have : 0 < (c - 2) ^ 2 / (2 * c) := by
      apply div_pos (by nlinarith) (by positivity)
    linarith

end GamblersFallacy

theorem solution (m : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    1 ≤ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) * (((m : ℝ) * p + 2) / ((i : ℝ) + 2)) ∧
      (1 ≤ m → 1 < ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) * (((m : ℝ) * p + 2) / ((i : ℝ) + 2))) :=
  GamblersFallacy.proposition_2_last_inequality m p hp
