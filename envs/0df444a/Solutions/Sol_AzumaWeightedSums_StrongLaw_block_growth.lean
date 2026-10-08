-- Prove2me | solution 1 for AzumaWeightedSums.StrongLaw.block_growth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:13:59.736868+00:00
-- url     : https://prove2.me/submissions/da471b85-a538-47c2-8f82-5983c2bd6e25

import Mathlib
import Definitions.Def_AzumaWeightedSums_StrongLaw_ReversedSum

namespace BG9817455d

open AzumaWeightedSums.StrongLaw

theorem A_succ (a : ℕ → ℝ) (n : ℕ) : A a (n + 1) = A a n + a (n + 1) := by
  unfold A
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem A_mono (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {m n : ℕ} (h : m ≤ n) :
    A a m ≤ A a n := by
  unfold A
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · intro i hi _
    simp only [Finset.mem_Icc] at hi
    exact (ha_pos i hi.1).le

theorem A_pos (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {n : ℕ} (h : 1 ≤ n) :
    0 < A a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [A_succ]
  have := A_mono a ha_pos (Nat.zero_le m)
  have h0 : A a 0 = 0 := by simp [A]
  have := ha_pos (m + 1) (by omega)
  linarith

end BG9817455d

open AzumaWeightedSums.StrongLaw in
theorem solution (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ε : ℝ) (hε : 0 < ε) (nk : ℕ → ℕ)
    (h411 : 2 * (3 + ε) / (6 + ε) < A a (nk 1))
    (h412 : ∀ n : ℕ, nk 1 < n → a n / A a n < ε / (6 + ε))
    (h414 : ∀ k : ℕ, 2 ≤ k →
        A a (nk (k - 1)) < A a (nk k) ∧ A a (nk k) ≤ (1 + ε / 3) * A a (nk (k - 1)) ∧
          (1 + ε / 3) * A a (nk (k - 1)) < A a (nk k + 1)) :
    ∀ k : ℕ, 1 ≤ k → (2 * (3 + ε) / (6 + ε)) ^ (k - 1) < A a (nk k) := by
  have hmono : ∀ k : ℕ, 1 ≤ k → nk 1 ≤ nk k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih =>
      have h := (h414 (k + 1) (by omega)).1
      simp only [Nat.add_sub_cancel] at h
      have : nk k ≤ nk (k + 1) := by
        by_contra hc
        rw [not_le] at hc
        have := BG9817455d.A_mono a ha_pos hc.le
        linarith
      omega
  have hc : 0 < 2 * (3 + ε) / (6 + ε) := by positivity
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 : (1 : ℝ) < 2 * (3 + ε) / (6 + ε) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    simp only [Nat.sub_self, pow_zero]
    linarith
  | succ k hk ih =>
    obtain ⟨_, _, h3⟩ := h414 (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h3 ⊢
    set n := nk (k + 1) + 1 with hn
    have hnpos : 0 < A a n := BG9817455d.A_pos a ha_pos (by omega)
    have h4 := h412 n (by have := hmono (k + 1) (by omega); omega)
    rw [div_lt_div_iff₀ hnpos (by positivity)] at h4
    have hAn : A a n = A a (nk (k + 1)) + a n := BG9817455d.A_succ a _
    rw [hAn] at h4 h3
    set X := A a (nk (k + 1))
    set Y := A a (nk k)
    have h5 : 6 * a n < ε * X := by nlinarith
    have h6 : (6 + 2 * ε) * Y < (6 + ε) * X := by nlinarith
    have h7 : Y * (2 * (3 + ε) / (6 + ε)) < X := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    have hk' : k = (k - 1) + 1 := by omega
    rw [hk', pow_succ]
    calc (2 * (3 + ε) / (6 + ε)) ^ (k - 1) * (2 * (3 + ε) / (6 + ε))
        < Y * (2 * (3 + ε) / (6 + ε)) := mul_lt_mul_of_pos_right ih hc
      _ < X := h7
