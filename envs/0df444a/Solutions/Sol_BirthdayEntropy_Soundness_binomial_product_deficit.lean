-- Prove2me | solution 1 for BirthdayEntropy.Soundness.binomial_product_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:03:23.711524+00:00
-- url     : https://prove2.me/submissions/ddd1f223-0b2d-4a78-9aca-b7178c2ee824

import Mathlib
noncomputable section
open scoped Classical

private lemma choose_step (a k : ℕ) (h : k ≤ a) :
    (Nat.choose a (k+1) : ℝ) = (Nat.choose a k : ℝ) * ((a : ℝ)-k) / (k+1) := by
  have heq := Nat.choose_succ_right_eq a k
  have hc : (Nat.choose a (k+1) : ℝ) * (k+1) = (Nat.choose a k : ℝ) * ((a : ℝ)-k) := by
    exact_mod_cast heq
  apply (eq_div_iff (by positivity : (k : ℝ)+1 ≠ 0)).mpr
  exact hc

private lemma factor_deficit (a b n k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (ha : k < a) (hb : k < b) (hn : k < n) (hs : (a : ℝ)+b+t ≤ 2*n) :
    (((a : ℝ)-k)*((b : ℝ)-k)/((n : ℝ)-k)^2) ≤ Real.exp (-t/n) := by
  have han : 0 < (a : ℝ)-k := sub_pos.mpr (by exact_mod_cast ha)
  have hbn : 0 < (b : ℝ)-k := sub_pos.mpr (by exact_mod_cast hb)
  have hnn : 0 < (n : ℝ)-k := sub_pos.mpr (by exact_mod_cast hn)
  have hnp : 0 < (n : ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le k) hn
  have hA := Real.log_le_sub_one_of_pos (div_pos han hnn)
  have hB := Real.log_le_sub_one_of_pos (div_pos hbn hnn)
  have hsum : Real.log (((a : ℝ)-k)/((n : ℝ)-k)) + Real.log (((b : ℝ)-k)/((n : ℝ)-k)) ≤ -t/n := by
    have hfrac : (((a : ℝ)-k)/((n : ℝ)-k)-1) + (((b : ℝ)-k)/((n : ℝ)-k)-1) ≤ -t/n := by
      apply (le_div_iff₀ hnp).mpr
      apply (mul_le_mul_iff_right₀ hnn).mp
      field_simp
      have hk : 0 ≤ (k : ℝ) := by positivity
      nlinarith [mul_nonneg ht hk, mul_le_mul_of_nonneg_left hs hnp.le]
    linarith
  have hlog : Real.log (((a : ℝ)-k)*((b : ℝ)-k)/((n : ℝ)-k)^2) =
      Real.log (((a : ℝ)-k)/((n : ℝ)-k)) + Real.log (((b : ℝ)-k)/((n : ℝ)-k)) := by
    rw [←Real.log_mul (div_pos han hnn).ne' (div_pos hbn hnn).ne']
    congr 1
    field_simp
  have hp : 0 < (((a : ℝ)-k)*((b : ℝ)-k)/((n : ℝ)-k)^2) := by positivity
  rw [←Real.exp_log hp]
  exact Real.exp_le_exp.mpr (hlog.trans_le hsum)

theorem solution (a b n ℓ : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (ha : ℓ ≤ a) (hb : ℓ ≤ b) (hn : ℓ ≤ n) (hs : (a : ℝ)+b+t ≤ 2*n) :
    (Nat.choose a ℓ : ℝ) * (Nat.choose b ℓ : ℝ) ≤ (Nat.choose n ℓ : ℝ)^2 *
      Real.exp (-(ℓ : ℝ)*t/n) := by
  induction ℓ with
  | zero => simp
  | succ k ih =>
    have hka : k < a := lt_of_lt_of_le (Nat.lt_succ_self _) ha
    have hkb : k < b := lt_of_lt_of_le (Nat.lt_succ_self _) hb
    have hkn : k < n := lt_of_lt_of_le (Nat.lt_succ_self _) hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le k) hkn
    have hnk : (0 : ℝ) < (n : ℝ)-k := sub_pos.mpr (by exact_mod_cast hkn)
    have hak : (0 : ℝ) ≤ (a : ℝ)-k := sub_nonneg.mpr (by exact_mod_cast hka.le)
    have hbk : (0 : ℝ) ≤ (b : ℝ)-k := sub_nonneg.mpr (by exact_mod_cast hkb.le)
    have hbase := ih hka.le hkb.le hkn.le
    have hfactor := factor_deficit a b n k t ht hka hkb hkn hs
    rw [choose_step a k hka.le,choose_step b k hkb.le,choose_step n k hkn.le]
    calc
      _ = ((Nat.choose a k : ℝ)*(Nat.choose b k : ℝ)) *
          (((a : ℝ)-k)*((b : ℝ)-k)/(k+1)^2) := by field_simp <;> ring
      _ ≤ ((Nat.choose n k : ℝ)^2 * Real.exp (-(k : ℝ)*t/n)) *
          (((a : ℝ)-k)*((b : ℝ)-k)/(k+1)^2) := by gcongr
      _ = ((Nat.choose n k : ℝ)*((n : ℝ)-k)/(k+1))^2 *
          Real.exp (-(k : ℝ)*t/n) * (((a : ℝ)-k)*((b : ℝ)-k)/((n : ℝ)-k)^2) := by
          field_simp
          <;> ring
      _ ≤ ((Nat.choose n k : ℝ)*((n : ℝ)-k)/(k+1))^2 *
          Real.exp (-(k : ℝ)*t/n) * Real.exp (-t/n) := by gcongr
      _ = _ := by
        rw [mul_assoc,←Real.exp_add]
        congr 2
        push_cast
        ring
