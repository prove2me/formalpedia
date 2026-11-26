-- Prove2me | solution 1 for Erdos287.weighted_progression_error_le_variation
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T21:56:05.649555+00:00
-- url     : https://prove2.me/submissions/5e8df2cd-1355-45fb-be11-4861e97ca81d

import Mathlib

open Finset

set_option autoImplicit false

private theorem weighted_prefix_identity (a f : ℕ → ℝ) (N : ℕ) :
    let P := fun n => ∑ j ∈ range n, a j
    (∑ j ∈ range N, (f j - f (j + 1)) * P (j + 1)) =
      (∑ j ∈ range N, f j * a j) - f N * P N := by
  dsimp only
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (f := fun j => f j * a j)]
    rw [sum_range_succ (f := a)]
    ring

private theorem prefix_error (q r n : ℕ) (hq : 0 < q) :
    |∑ j ∈ range n, ((if j ≡ r [MOD q] then (1 : ℝ) else 0) - 1 / (q : ℝ))| ≤ 1 := by
  have hcnt :
      (∑ j ∈ range n, if j ≡ r [MOD q] then (1 : ℝ) else 0) =
        ((n / q : ℕ) : ℝ) + (if r % q < n % q then 1 else 0) := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card n hq]
    push_cast
    split_ifs <;> rfl
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr : ((n % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt n hq
  have hdiv : (n : ℝ) / q = ((n / q : ℕ) : ℝ) + ((n % q : ℕ) : ℝ) / q := by
    have h := (show (q : ℝ) * ((n / q : ℕ) : ℝ) + ((n % q : ℕ) : ℝ) = n from
      by exact_mod_cast Nat.div_add_mod n q)
    apply (div_eq_iff hq0.ne').mpr
    calc
      (n : ℝ) = (q : ℝ) * ((n / q : ℕ) : ℝ) + ((n % q : ℕ) : ℝ) := h.symm
      _ = (((n / q : ℕ) : ℝ) + ((n % q : ℕ) : ℝ) / q) * q := by
        rw [add_mul, div_mul_cancel₀ _ hq0.ne']
        ring
  rw [sum_sub_distrib, hcnt]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one_div]
  rw [hdiv]
  have hlo : (0 : ℝ) ≤ ((n % q : ℕ) : ℝ) / q := by positivity
  have hhi : ((n % q : ℕ) : ℝ) / q ≤ 1 := (div_le_one hq0).mpr hqr.le
  apply abs_le.mpr
  split_ifs <;> constructor <;> linarith

/-- The discrepancy of a weighted residue class from the uniform mean
is bounded by the total variation, including the terminal step to zero. -/
theorem solution (q r N : ℕ) (hq : 0 < q) (f : ℕ → ℝ) (hzero : f N = 0) :
    |(∑ j ∈ Finset.range N, if Nat.ModEq q j r then f j else 0) -
        (∑ j ∈ Finset.range N, f j) / (q : ℝ)| ≤
      ∑ j ∈ Finset.range N, |f (j + 1) - f j| := by
  let a (j : ℕ) := (if j ≡ r [MOD q] then (1 : ℝ) else 0) - 1 / (q : ℝ)
  let P (j : ℕ) := ∑ l ∈ range j, a l
  have hP (j : ℕ) : |P j| ≤ 1 := prefix_error q r j hq
  have hweight :
      (∑ j ∈ range N, if j ≡ r [MOD q] then f j else 0) -
        (∑ j ∈ range N, f j) / (q : ℝ) = ∑ j ∈ range N, f j * a j := by
    simp only [a, mul_sub, mul_one_div, sum_sub_distrib, sum_div]
    congr 1
    apply sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hparts :
      (∑ j ∈ range N, (f j - f (j + 1)) * P (j + 1)) = ∑ j ∈ range N, f j * a j := by
    simpa only [hzero, zero_mul, sub_zero] using weighted_prefix_identity a f N
  rw [hweight, ← hparts]
  calc
    _ ≤ ∑ j ∈ range N, |(f j - f (j + 1)) * P (j + 1)| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro j _
      rw [abs_mul, abs_sub_comm (f j)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hP (j + 1))

