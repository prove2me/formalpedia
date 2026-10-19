-- Prove2me | solution 1 for BnBPEP.WeakCvx.eq_45
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:24:52.961712+00:00
-- url     : https://prove2.me/submissions/ffca4f1c-0faf-42c8-a82a-88a1e6850608

import Mathlib
set_option autoImplicit false

theorem solution (N : ℕ) (h L κ : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 2) (hL : 0 < L) (b c : ℕ → ℝ)
    (hrec : ∀ k ≤ N, 4 + (1 - 2 * h) * b (k + 1) = b k) (hterm : b (N + 1) = 0)
    (hc : ∀ k ≤ N, c k = h ^ 2 * b (k + 1)) :
    L ^ 2 / ((N : ℝ) + 1) * (∑ i ∈ Finset.range (N + 1), c i + κ ^ 2 * b 0)
      = L ^ 2 / ((N : ℝ) + 1) * (-1 + (1 - 2 * h) ^ (N + 1) + 2 * h * ((N : ℝ) + 1)
          + κ ^ 2 * (2 / h) * (1 - (1 - 2 * h) ^ (N + 1))) := by
  have hne : h ≠ 0 := hh0.ne'
  -- closed form of b
  have key : ∀ j : ℕ, j ≤ N + 1 → b (N + 1 - j) = (2 / h) * (1 - (1 - 2 * h) ^ j) := by
    intro j
    induction j with
    | zero => intro _; simp [hterm]
    | succ j ih =>
      intro hj
      have h1 : N + 1 - (j + 1) ≤ N := by omega
      have h2 : N + 1 - (j + 1) + 1 = N + 1 - j := by omega
      have := hrec _ h1
      rw [h2, ih (by omega)] at this
      rw [← this]
      field_simp
      ring
  have hb0 : b 0 = (2 / h) * (1 - (1 - 2 * h) ^ (N + 1)) := by
    have := key (N + 1) le_rfl
    simpa using this
  have hsum : ∑ i ∈ Finset.range (N + 1), c i
      = ∑ i ∈ Finset.range (N + 1), h ^ 2 * ((2 / h) * (1 - (1 - 2 * h) ^ (N - i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ N := by have := Finset.mem_range.mp hi; omega
    rw [hc i hi']
    have := key (N - i) (by omega)
    have e : N + 1 - (N - i) = i + 1 := by omega
    rw [e] at this
    rw [this]
  have hgeom : ∑ i ∈ Finset.range (N + 1), (1 - 2 * h) ^ (N - i)
      = (1 - (1 - 2 * h) ^ (N + 1)) / (2 * h) := by
    rw [← Finset.sum_range_reflect]
    have : ∀ j ∈ Finset.range (N + 1), (1 - 2 * h) ^ (N - (N + 1 - 1 - j)) = (1 - 2 * h) ^ j := by
      intro j hj
      have := Finset.mem_range.mp hj
      congr 1; omega
    rw [Finset.sum_congr rfl this, geom_sum_eq (by intro hh1; apply hne; linarith)]
    have : (1 - 2 * h) - 1 = -(2 * h) := by ring
    rw [this]
    field_simp
    ring
  have hS : ∑ i ∈ Finset.range (N + 1), c i
      = -1 + (1 - 2 * h) ^ (N + 1) + 2 * h * ((N : ℝ) + 1) := by
    rw [hsum]
    have : ∀ i ∈ Finset.range (N + 1), h ^ 2 * ((2 / h) * (1 - (1 - 2 * h) ^ (N - i)))
        = 2 * h - 2 * h * (1 - 2 * h) ^ (N - i) := by
      intro i _
      field_simp
    have hm : ∑ x ∈ Finset.range (N + 1), 2 * h * (1 - 2 * h) ^ (N - x)
        = 2 * h * ∑ x ∈ Finset.range (N + 1), (1 - 2 * h) ^ (N - x) := by
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, hm, hgeom]
    simp
    field_simp
    ring
  rw [hS, hb0]
  ring
