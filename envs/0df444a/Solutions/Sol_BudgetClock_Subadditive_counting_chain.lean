-- Prove2me | solution 1 for BudgetClock.Subadditive.counting_chain
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:21:00.947794+00:00
-- url     : https://prove2.me/submissions/cedce0cd-b1d8-4e9a-a2f3-69d926f3c56c

import Mathlib
set_option autoImplicit false

theorem solution (r : ℕ) (hr : 1 ≤ r) (z : ℕ → ℕ)
    (hz : ∀ i, 1 ≤ i → i ≤ r → 1 ≤ z i)
    (hchain : 1 / ((z 1 : ℝ) + 1) +
        ∑ i ∈ Finset.Ico 1 r, (z i : ℝ) / ((z (i + 1) : ℝ) + 1) ≤ 1) :
    ((r : ℝ) / 2) ^ r ≤ (z r : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  set t : ℕ → ℝ := fun j => if j = 0 then 1 / ((z 1 : ℝ) + 1)
    else (z j : ℝ) / ((z (j + 1) : ℝ) + 1) with ht
  have ht0 : ∀ j, 0 ≤ t j := by
    intro j; simp only [ht]; split_ifs <;> positivity
  have hsum : ∑ j ∈ Finset.range (n + 1), t j ≤ 1 := by
    rw [Finset.sum_range_succ']
    have h1 : ∑ i ∈ Finset.Ico 1 (n + 1), (z i : ℝ) / ((z (i + 1) : ℝ) + 1)
        = ∑ j ∈ Finset.range n, t (j + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [ht, Nat.add_sub_cancel, add_comm 1]
      simp
    have h2 : t 0 = 1 / ((z 1 : ℝ) + 1) := by simp [ht]
    rw [h2]; linarith
  -- product identity
  have hprod : ∀ k, ((∏ j ∈ Finset.range (k + 1), t j) * ((z (k + 1) : ℝ) + 1)
      = ∏ i ∈ Finset.Ico 1 (k + 1), (z i : ℝ) / ((z i : ℝ) + 1)) := by
    intro k
    induction k with
    | zero =>
      simp [ht]
      field_simp
    | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_Ico_succ_top (by omega)]
      have hpos : (0 : ℝ) < (z (k + 1) : ℝ) + 1 := by positivity
      have hpos2 : (0 : ℝ) < (z (k + 1 + 1) : ℝ) + 1 := by positivity
      have htk : t (k + 1) = (z (k + 1) : ℝ) / ((z (k + 1 + 1) : ℝ) + 1) := by
        simp [ht]
      rw [htk, ← ih]
      field_simp
  -- AM-GM
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hamgm : ∏ j ∈ Finset.range (n + 1), t j ≤ (1 / ((n : ℝ) + 1)) ^ (n + 1) := by
    have hw := Real.geom_mean_le_arith_mean_weighted (Finset.range (n + 1))
      (fun _ => 1 / ((n : ℝ) + 1)) t (fun _ _ => by positivity)
      (by simp; field_simp) (fun j _ => ht0 j)
    rw [Real.finset_prod_rpow _ _ (fun j _ => ht0 j)] at hw
    rw [← Finset.mul_sum] at hw
    have hw2 : (∏ j ∈ Finset.range (n + 1), t j) ^ (1 / ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
      calc _ ≤ _ := hw
        _ ≤ 1 / ((n : ℝ) + 1) * 1 := by
          apply mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := mul_one _
    have hP : 0 ≤ ∏ j ∈ Finset.range (n + 1), t j := Finset.prod_nonneg (fun j _ => ht0 j)
    have := pow_le_pow_left₀ (Real.rpow_nonneg hP _) hw2 (n + 1)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP] at this
    have e : 1 / ((n : ℝ) + 1) * ((n + 1 : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [e, Real.rpow_one] at this
    exact this
  -- lower bound on product
  have hlow : (1 / 2 : ℝ) ^ n ≤ ∏ i ∈ Finset.Ico 1 (n + 1), (z i : ℝ) / ((z i : ℝ) + 1) := by
    have := Finset.prod_le_prod (s := Finset.Ico 1 (n + 1)) (f := fun _ => (1 / 2 : ℝ))
      (g := fun i => (z i : ℝ) / ((z i : ℝ) + 1)) (fun _ _ => by norm_num) (by
        intro i hi
        rw [Finset.mem_Ico] at hi
        have h1 : (1 : ℝ) ≤ z i := by exact_mod_cast hz i hi.1 (by omega)
        show 1 / 2 ≤ (z i : ℝ) / ((z i : ℝ) + 1)
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith)
    simpa using this
  have hzpos : (0 : ℝ) < (z (n + 1) : ℝ) + 1 := by positivity
  have key : (1 / 2 : ℝ) ^ n ≤ (1 / ((n : ℝ) + 1)) ^ (n + 1) * ((z (n + 1) : ℝ) + 1) := by
    calc (1 / 2 : ℝ) ^ n ≤ _ := hlow
      _ = _ := (hprod n).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hamgm hzpos.le
  have h3 : ((n : ℝ) + 1) ^ (n + 1) ≤ 2 ^ n * ((z (n + 1) : ℝ) + 1) := by
    have hp : (0 : ℝ) < ((n : ℝ) + 1) ^ (n + 1) := by positivity
    have hq : (0 : ℝ) < 2 ^ n := by positivity
    rw [one_div, one_div, inv_pow, inv_pow, ← div_eq_inv_mul, inv_eq_one_div,
      div_le_div_iff₀ hq hp] at key
    nlinarith [key]
  have hA : ((((n + 1 : ℕ) : ℝ)) / 2) ^ (n + 1) = ((n : ℝ) + 1) ^ (n + 1) / 2 ^ (n + 1) := by
    push_cast; rw [div_pow]
  rcases Nat.eq_zero_or_pos n with h0 | hnpos
  · subst h0
    have := hz 1 le_rfl le_rfl
    have h1 : (1 : ℝ) ≤ z 1 := by exact_mod_cast this
    have e : ((((0 + 1 : ℕ) : ℝ)) / 2) ^ (0 + 1) = 1 / 2 := by norm_num
    rw [e]
    exact le_trans (by norm_num) h1
  · have hA1 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) / 2) ^ (n + 1) := by
      apply one_le_pow₀
      have : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      push_cast; linarith
    rw [hA] at hA1 ⊢
    have h4 : ((n : ℝ) + 1) ^ (n + 1) / 2 ^ (n + 1) ≤ ((z (n + 1) : ℝ) + 1) / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [pow_succ (2 : ℝ) n]
      nlinarith [h3]
    linarith
