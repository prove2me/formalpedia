-- Prove2me | solution 1 for Erdos287.log_ratio_bound_with_unit_gaps
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T05:20:32.219302+00:00
-- url     : https://prove2.me/submissions/0bcbe000-67c1-439c-8db6-5de76e96d7b5

import Mathlib

open Finset

set_option autoImplicit false

/-- The unit gaps improve the logarithmic bound on the ratio of the extreme
denominators. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) :
    Real.log ((f (k - 1) : ℝ) / f 0) +
      ((((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card : ℝ) + 2) /
        f (k - 1) ≤ 2 := by
  let M := f (k - 1)
  let U := (range (k - 1)).filter (fun i => f (i + 1) - f i = 1)
  change Real.log ((M : ℝ) / f 0) + ((U.card : ℝ) + 2) / M ≤ 2
  have hpos (i : ℕ) (hi : i < k) : (0 : ℝ) < f i :=
    Nat.cast_pos.mpr (by have := hf1 i hi; omega)
  have hM : (0 : ℝ) < M := hpos _ (by omega)
  have hsumR : ∑ i ∈ range k, (1 : ℝ) / f i = 1 := by
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using
      congrArg (fun q : ℚ => (q : ℝ)) hsum
  have hsumCut : ∑ i ∈ range (k - 1), (1 : ℝ) / f i = 1 - 1 / M := by
    have hsplit := sum_range_succ (fun i => (1 : ℝ) / f i) (k - 1)
    rw [show k - 1 + 1 = k by omega, hsumR] at hsplit
    linarith only [hsplit]
  have htel :
      (∑ i ∈ range (k - 1), Real.log ((f (i + 1) : ℝ) / f i)) =
        Real.log ((M : ℝ) / f 0) := by
    calc
      _ = ∑ i ∈ range (k - 1), (Real.log (f (i + 1) : ℝ) - Real.log (f i : ℝ)) := by
        apply sum_congr rfl
        intro i hi
        have hir := mem_range.mp hi
        exact Real.log_div (hpos _ (by omega)).ne' (hpos _ (by omega)).ne'
      _ = Real.log (M : ℝ) - Real.log (f 0 : ℝ) :=
        sum_range_sub (fun i => Real.log (f i : ℝ)) (k - 1)
      _ = _ := (Real.log_div hM.ne' (hpos 0 (by omega)).ne').symm
  have hcount : (∑ i ∈ range (k - 1), if f (i + 1) - f i = 1 then (1 : ℝ) / M else 0) =
      (U.card : ℝ) / M := by
    rw [← sum_filter]
    simp [U, div_eq_mul_inv]
  have hstep (i : ℕ) (hi : i ∈ range (k - 1)) :
      Real.log ((f (i + 1) : ℝ) / f i) +
        (if f (i + 1) - f i = 1 then (1 : ℝ) / M else 0) ≤ 2 * ((1 : ℝ) / f i) := by
    have hir := mem_range.mp hi
    have hlt := hmono i (i + 1) (by omega) (by omega)
    have hcast :
        ((f (i + 1) - f i : ℕ) : ℝ) = (f (i + 1) : ℝ) - f i := Nat.cast_sub hlt.le
    have hlog :
        Real.log ((f (i + 1) : ℝ) / f i) ≤ ((f (i + 1) - f i : ℕ) : ℝ) / f i := by
      calc
        _ ≤ (f (i + 1) : ℝ) / f i - 1 :=
          Real.log_le_sub_one_of_pos (div_pos (hpos _ (by omega)) (hpos _ (by omega)))
        _ = _ := by rw [hcast, sub_div, div_self (hpos _ (by omega)).ne']
    have hg := hgap i (by omega)
    have hfi : f i < M := hmono i (k - 1) hir (by omega)
    have hrecip : (1 : ℝ) / M ≤ 1 / f i :=
      one_div_le_one_div_of_le (hpos _ (by omega)) (by exact_mod_cast hfi.le)
    rcases (show f (i + 1) - f i = 1 ∨ f (i + 1) - f i = 2 by omega) with hd | hd
    · simp only [hd, Nat.cast_one] at hlog
      simp only [hd, if_true]
      linarith
    · simp only [hd, Nat.cast_ofNat] at hlog
      rw [if_neg (show f (i + 1) - f i ≠ 1 by omega), add_zero]
      simpa only [mul_one_div] using hlog
  have htotal := sum_le_sum hstep
  rw [sum_add_distrib, htel, hcount, ← mul_sum, hsumCut] at htotal
  calc
    _ = (Real.log ((M : ℝ) / f 0) + (U.card : ℝ) / M) + 2 / M := by
      rw [add_div, add_assoc]
    _ ≤ 2 * (1 - 1 / (M : ℝ)) + 2 / M := add_le_add htotal le_rfl
    _ = 2 := by ring

