-- Prove2me | solution 1 for GamblersFallacy.eq_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:31:36.461307+00:00
-- url     : https://prove2.me/submissions/9fc76dba-7643-409e-b7f1-d6fde569b210

import Mathlib

theorem solution (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    1 < ((m : ℝ) * p + 2) *
      ∑ i ∈ Finset.Icc 1 m,
        ((m - 1).choose (i - 1) : ℝ) * p ^ (i - 1) * (1 - p) ^ (m - i) / ((i : ℝ) + 1) := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hreidx : ∀ (f : ℕ → ℝ) (N : ℕ), ∑ i ∈ Finset.Icc 1 N, f i = ∑ k ∈ Finset.range N, f (k + 1) := by
    intro f N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  rw [hreidx]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((n + 1 - 1).choose (k + 1 - 1) : ℝ) * p ^ (k + 1 - 1) * (1 - p) ^ (n + 1 - (k + 1)) /
        (((k + 1 : ℕ) : ℝ) + 1) = ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) / ((k : ℝ) + 2) := by
    intro k _
    rw [show n + 1 - 1 = n by omega, show k + 1 - 1 = k by omega,
      show n + 1 - (k + 1) = n - k by omega]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  set w : ℕ → ℝ := fun k => (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by
    simp only [hw]
    have : 0 ≤ 1 - p := by linarith
    positivity
  have hw1 : ∑ k ∈ Finset.range (n + 1), w k = 1 := by
    have h := add_pow p (1 - p) n
    rw [show p + (1 - p) = 1 by ring, one_pow] at h
    rw [h]
    exact Finset.sum_congr rfl (fun k _ => by simp only [hw]; ring)
  have hmean : ∑ k ∈ Finset.range (n + 1), (k : ℝ) * w k = n * p := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have h := add_pow p (1 - p) n'
    rw [show p + (1 - p) = 1 by ring, one_pow] at h
    have hk : ∀ k ∈ Finset.range (n' + 1), ((k + 1 : ℕ) : ℝ) * w (k + 1) =
        ((n' : ℝ) + 1) * p * (p ^ k * (1 - p) ^ (n' - k) * (n'.choose k : ℝ)) := by
      intro k _
      simp only [hw]
      have hc : ((n' + 1 : ℕ) : ℝ) * (n'.choose k : ℝ) =
          ((n' + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_one_mul_choose_eq n' k
      rw [show n' + 1 - (k + 1) = n' - k by omega]
      push_cast at hc ⊢
      rw [pow_succ]
      linear_combination (p ^ k * p * (1 - p) ^ (n' - k)) * hc.symm
    rw [Finset.sum_congr rfl hk, ← Finset.mul_sum, ← h]
    push_cast
    ring
  have hb : 0 < (n : ℝ) * p + 2 := by positivity
  have htan : ∀ k ∈ Finset.range (n + 1),
      w k * (2 / ((n : ℝ) * p + 2) - ((k : ℝ) + 2) / ((n : ℝ) * p + 2) ^ 2) ≤ w k / ((k : ℝ) + 2) := by
    intro k _
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hineq : 2 / ((n : ℝ) * p + 2) - ((k : ℝ) + 2) / ((n : ℝ) * p + 2) ^ 2 ≤ 1 / ((k : ℝ) + 2) := by
      rw [div_sub_div _ _ hb.ne' (by positivity), div_le_div_iff₀ (by positivity) hk2]
      nlinarith [sq_nonneg ((k : ℝ) + 2 - ((n : ℝ) * p + 2)), sq_nonneg ((n : ℝ) * p + 2)]
    calc w k * (2 / ((n : ℝ) * p + 2) - ((k : ℝ) + 2) / ((n : ℝ) * p + 2) ^ 2)
        ≤ w k * (1 / ((k : ℝ) + 2)) := mul_le_mul_of_nonneg_left hineq (hw0 k)
      _ = w k / ((k : ℝ) + 2) := by ring
  have hlow : 1 / ((n : ℝ) * p + 2) ≤ ∑ k ∈ Finset.range (n + 1), w k / ((k : ℝ) + 2) := by
    calc 1 / ((n : ℝ) * p + 2)
        = ∑ k ∈ Finset.range (n + 1),
            w k * (2 / ((n : ℝ) * p + 2) - ((k : ℝ) + 2) / ((n : ℝ) * p + 2) ^ 2) := by
          have e : ∀ k ∈ Finset.range (n + 1),
              w k * (2 / ((n : ℝ) * p + 2) - ((k : ℝ) + 2) / ((n : ℝ) * p + 2) ^ 2) =
              (2 / ((n : ℝ) * p + 2) - 2 / ((n : ℝ) * p + 2) ^ 2) * w k -
                (1 / ((n : ℝ) * p + 2) ^ 2) * ((k : ℝ) * w k) := by
            intro k _
            ring
          rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            hw1, hmean]
          field_simp <;> ring
      _ ≤ ∑ k ∈ Finset.range (n + 1), w k / ((k : ℝ) + 2) := Finset.sum_le_sum htan
  have hfin : 1 < (((n + 1 : ℕ) : ℝ) * p + 2) * (1 / ((n : ℝ) * p + 2)) := by
    rw [mul_one_div, lt_div_iff₀ hb]
    push_cast
    linarith
  calc (1 : ℝ) < (((n + 1 : ℕ) : ℝ) * p + 2) * (1 / ((n : ℝ) * p + 2)) := hfin
    _ ≤ (((n + 1 : ℕ) : ℝ) * p + 2) * ∑ k ∈ Finset.range (n + 1), w k / ((k : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
