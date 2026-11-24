-- Prove2me | solution 1 for BB6Kit.excl_215
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T22:49:53.086299+00:00
-- url     : https://prove2.me/submissions/7ceee75d-2938-4b82-85da-74719342c613

import Mathlib
import Definitions.Def_BB6Kit

namespace BB6KitEx

theorem big (n : ℕ) (hn : 60 ≤ n) : 2 ^ 26 * n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
    calc 2 ^ 26 * (m + 1) ^ 2 ≤ 2 * (2 ^ 26 * m ^ 2) := by nlinarith
      _ < 2 * 2 ^ m := by omega
      _ = 2 ^ (m + 1) := by ring

theorem small_form (u1 u3 : ℤ) (h1 : -8 ≤ u1) (h1' : u1 ≤ 8) (h3 : -8 ≤ u3) (h3' : u3 ≤ 8)
    (hne : ¬ (u1 = 0 ∧ u3 = 0)) : 1 / 25 ≤ |(u1 : ℝ) * Real.log 3 + (u3 : ℝ) * Real.log 2| := by
  by_contra h
  push_neg at h
  have hxpos : (0:ℝ) < (3:ℝ) ^ u1 * (2:ℝ) ^ u3 := by positivity
  have hlogx : Real.log ((3:ℝ) ^ u1 * (2:ℝ) ^ u3) = (u1 : ℝ) * Real.log 3 + (u3 : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_zpow, Real.log_zpow]
  rw [← hlogx] at h
  have hlo : (24:ℝ) / 25 < (3:ℝ) ^ u1 * (2:ℝ) ^ u3 := by
    have h1 : -(1/25 : ℝ) < Real.log ((3:ℝ) ^ u1 * (2:ℝ) ^ u3) := by
      linarith [neg_abs_le (Real.log ((3:ℝ) ^ u1 * (2:ℝ) ^ u3))]
    have h2 : Real.exp (-(1/25)) < (3:ℝ) ^ u1 * (2:ℝ) ^ u3 := by
      have := Real.exp_lt_exp.mpr h1; rwa [Real.exp_log hxpos] at this
    have h3 := Real.add_one_le_exp (-(1/25 : ℝ))
    linarith
  have hhi : (3:ℝ) ^ u1 * (2:ℝ) ^ u3 < 25 / 24 := by
    have h1 : Real.log ((3:ℝ) ^ u1 * (2:ℝ) ^ u3) < 1/25 := lt_of_le_of_lt (le_abs_self _) h
    have h2 : (3:ℝ) ^ u1 * (2:ℝ) ^ u3 < Real.exp (1/25) := by
      have := Real.exp_lt_exp.mpr h1; rwa [Real.exp_log hxpos] at this
    have h3 := Real.add_one_le_exp (-(1/25 : ℝ))
    have h4 : Real.exp (1/25) * Real.exp (-(1/25)) = 1 := by rw [← Real.exp_add]; simp
    have h5 : 0 < Real.exp (1/25 : ℝ) := Real.exp_pos _
    have h6 : Real.exp (1/25) ≤ 25 / 24 := by nlinarith
    linarith
  interval_cases u1 <;> interval_cases u3 <;>
    first | (norm_num at hne; done) | (norm_num at hlo; done) | (norm_num at hhi; done)

end BB6KitEx

set_option maxHeartbeats 400000 in
theorem solution (n i k c : ℕ) (hn : 60 ≤ n) (hi : 2 ^ n ≤ i) (hi' : i < 2 ^ (n + 1))
    (hc : 0 < c) (hc4 : c ≤ 4 * i) (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2)
    (hsmall : |((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ)| < 1) :
    ¬ (∃ u1 u2 u3 : ℤ, u1 * ((k - 1 : ℕ) : ℤ) + u2 * ((1 : ℕ) : ℤ) + u3 * ((i) : ℤ) = 0 ∧ Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 ∧
        (|u1| : ℝ) ≤ (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1) / ((max (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fS1 n) + 1) (((BB6Kit.fS1 n) : ℝ) + (BB6Kit.fR1 n) + 1)) (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fR1 n) + 1) ((BB6Kit.fChi n) * Real.sqrt ((((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1))))) - max ((BB6Kit.fS1 n) : ℝ) (BB6Kit.fR1 n)) ∧
        (|u2| : ℝ) ≤ (((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1) / ((max (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fS1 n) + 1) (((BB6Kit.fS1 n) : ℝ) + (BB6Kit.fR1 n) + 1)) (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fR1 n) + 1) ((BB6Kit.fChi n) * Real.sqrt ((((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1))))) - max ((BB6Kit.fR1 n) : ℝ) (BB6Kit.fR1 n)) ∧
        (|u3| : ℝ) ≤ (((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) / ((max (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fS1 n) + 1) (((BB6Kit.fS1 n) : ℝ) + (BB6Kit.fR1 n) + 1)) (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fR1 n) + 1) ((BB6Kit.fChi n) * Real.sqrt ((((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1))))) - max ((BB6Kit.fR1 n) : ℝ) (BB6Kit.fS1 n))) := by
  rintro ⟨u1, u2, u3, hrel, hgcd, hu1, hu2, hu3⟩
  have hK : BB6Kit.fK n = 2 ^ 23 * n ^ 2 := rfl
  have hR1 : BB6Kit.fR1 n = 2 ^ 20 * n ^ 2 := by
    show 2 ^ 23 * n ^ 2 / 8 = _
    rw [show 2 ^ 23 * n ^ 2 = 2 ^ 20 * n ^ 2 * 8 by ring]; exact Nat.mul_div_cancel _ (by norm_num)
  have hS1 : BB6Kit.fS1 n = 80 := rfl
  have hM0 : BB6Kit.fM0 n = ((2 ^ 20 * n ^ 2 + 1) * 81 * (2 ^ 20 * n ^ 2 + 1) - 1) / (2 ^ 23 * n ^ 2) := by
    show ((BB6Kit.fR1 n + 1) * (BB6Kit.fS1 n + 1) * (BB6Kit.fR1 n + 1) - 1) / BB6Kit.fK n = _
    rw [hR1, hS1, hK]
  have hn2 : 3600 ≤ n ^ 2 := by nlinarith
  have hKpos : 0 < 2 ^ 23 * n ^ 2 := by positivity
  have hM0big : 10 * (2 ^ 20 * n ^ 2) + 10 ≤ BB6Kit.fM0 n := by
    rw [hM0, Nat.le_div_iff_mul_le hKpos]
    have : (10 * (2 ^ 20 * n ^ 2) + 10) * (2 ^ 23 * n ^ 2) + 1 ≤
        (2 ^ 20 * n ^ 2 + 1) * 81 * (2 ^ 20 * n ^ 2 + 1) := by nlinarith
    omega
  have hV1pos : (0:ℝ) < ((BB6Kit.fR1 n : ℝ) + 1) * ((BB6Kit.fS1 n : ℝ) + 1) * ((BB6Kit.fR1 n : ℝ) + 1) := by
    positivity
  have hchiV : BB6Kit.fChi n * Real.sqrt (((BB6Kit.fR1 n : ℝ) + 1) * ((BB6Kit.fS1 n : ℝ) + 1) *
      ((BB6Kit.fR1 n : ℝ) + 1)) = (BB6Kit.fM0 n : ℝ) := by
    unfold BB6Kit.fChi
    push_cast
    rw [div_mul_cancel₀]
    exact (Real.sqrt_pos.mpr hV1pos).ne'
  rw [hchiV] at hu1 hu2 hu3
  -- real abbreviations
  have hr : (BB6Kit.fR1 n : ℝ) = 2 ^ 20 * (n : ℝ) ^ 2 := by rw [hR1]; push_cast; ring
  have hs : (BB6Kit.fS1 n : ℝ) = 80 := by rw [hS1]; norm_num
  have hm : 10 * (BB6Kit.fR1 n : ℝ) + 10 ≤ (BB6Kit.fM0 n : ℝ) := by
    have : 10 * BB6Kit.fR1 n + 10 ≤ BB6Kit.fM0 n := by rw [hR1]; exact hM0big
    exact_mod_cast this
  have hr80 : (80:ℝ) ≤ (BB6Kit.fR1 n : ℝ) := by
    rw [hr]; have : (3600:ℝ) ≤ (n:ℝ) ^ 2 := by exact_mod_cast hn2
    nlinarith
  have hr0 : (0:ℝ) ≤ (BB6Kit.fR1 n : ℝ) := by positivity
  rw [hs] at hu1 hu2 hu3
  have hmaxA : max ((BB6Kit.fR1 n : ℝ) + 80 + 1) (80 + (BB6Kit.fR1 n : ℝ) + 1) ≤
      max ((BB6Kit.fR1 n : ℝ) + (BB6Kit.fR1 n : ℝ) + 1) (BB6Kit.fM0 n : ℝ) :=
    max_le (le_trans (by linarith) (le_max_right _ _)) (le_trans (by linarith) (le_max_right _ _))
  rw [max_eq_right hmaxA, max_eq_right (by linarith : (BB6Kit.fR1 n : ℝ) + (BB6Kit.fR1 n : ℝ) + 1 ≤ (BB6Kit.fM0 n : ℝ))]
    at hu1 hu2 hu3
  rw [max_eq_right (by linarith : (80:ℝ) ≤ (BB6Kit.fR1 n : ℝ))] at hu1
  rw [max_self] at hu2
  rw [max_eq_left (by linarith : (80:ℝ) ≤ (BB6Kit.fR1 n : ℝ))] at hu3
  set r : ℝ := (BB6Kit.fR1 n : ℝ) with hrdef
  set m : ℝ := (BB6Kit.fM0 n : ℝ) with hmdef
  clear_value r m
  have hmr : 0 < m - r := by linarith
  have hU1 : (80 + 1) * (r + 1) / (m - r) < 9 := by
    rw [div_lt_iff₀ hmr]; linarith
  have hU2 : (r + 1) * (r + 1) / (m - r) ≤ r + 1 := by
    rw [div_le_iff₀ hmr]; nlinarith
  have hU3 : (r + 1) * (80 + 1) / (m - r) < 9 := by
    rw [div_lt_iff₀ hmr]; linarith
  have a1 : |(u1 : ℝ)| < 9 := lt_of_le_of_lt hu1 hU1
  have a3 : |(u3 : ℝ)| < 9 := lt_of_le_of_lt hu3 hU3
  have a2 : |(u2 : ℝ)| ≤ r + 1 := le_trans hu2 hU2
  have b1 : |u1| < 9 := by
    have : ((|u1| : ℤ) : ℝ) < 9 := by rw [Int.cast_abs]; exact a1
    exact_mod_cast this
  have b3 : |u3| < 9 := by
    have : ((|u3| : ℤ) : ℝ) < 9 := by rw [Int.cast_abs]; exact a3
    exact_mod_cast this
  obtain ⟨b1l, b1r⟩ := abs_lt.mp b1
  obtain ⟨b3l, b3r⟩ := abs_lt.mp b3
  -- real relation
  have hrelR : ((u1 * ((k - 1 : ℕ) : ℤ) + u2 * ((1 : ℕ) : ℤ) + u3 * (i : ℤ) : ℤ) : ℝ) = 0 := by
    rw [hrel]; simp
  push_cast [Nat.cast_sub (by omega : 1 ≤ k)] at hrelR
  set Λ : ℝ := ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ) with hΛ
  have key : (i : ℝ) * ((u1 : ℝ) * Real.log 3 + (u3 : ℝ) * Real.log 2) =
      (u1 : ℝ) * (Real.log (c : ℝ) - Λ) - (u2 : ℝ) * Real.log 2 := by
    rw [hΛ]; linear_combination (Real.log 2) * hrelR
  by_cases h0 : u1 = 0 ∧ u3 = 0
  · obtain ⟨rfl, rfl⟩ := h0
    have : u2 = 0 := by simpa using hrel
    subst this
    simp at hgcd
  have hsf := BB6KitEx.small_form u1 u3 (by omega) (by omega) (by omega) (by omega) h0
  -- bounds
  have hi0 : (0:ℝ) < (i : ℝ) := by
    have : 0 < i := lt_of_lt_of_le (by positivity) hi
    exact_mod_cast this
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hc1 : (1:ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hlogc0 : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg hc1
  have hlogc : Real.log (c : ℝ) ≤ ((n : ℝ) + 3) * Real.log 2 := by
    have h1 : (c : ℝ) ≤ (2:ℝ) ^ (n + 3) := by
      have : c ≤ 2 ^ (n + 3) := by
        have : 2 ^ (n + 3) = 4 * 2 ^ (n + 1) := by ring
        omega
      exact_mod_cast this
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    exact h2
  have hu1le : |(u1 : ℝ)| ≤ 8 := by
    have : |u1| ≤ 8 := by omega
    have h' : ((|u1| : ℤ) : ℝ) ≤ 8 := by exact_mod_cast this
    rwa [Int.cast_abs] at h'
  have hrhs : |(u1 : ℝ) * (Real.log (c : ℝ) - Λ) - (u2 : ℝ) * Real.log 2| ≤
      8 * (((n : ℝ) + 3) + 1) + (r + 1) := by
    have e1 : |(u1 : ℝ) * (Real.log (c : ℝ) - Λ)| ≤ 8 * (((n : ℝ) + 3) + 1) := by
      rw [abs_mul]
      have : |Real.log (c : ℝ) - Λ| ≤ ((n : ℝ) + 3) + 1 := by
        have := abs_sub (Real.log (c : ℝ)) Λ
        rw [abs_of_nonneg hlogc0] at this
        nlinarith
      exact mul_le_mul hu1le this (abs_nonneg _) (by norm_num)
    have e2 : |(u2 : ℝ) * Real.log 2| ≤ r + 1 := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < Real.log 2)]
      nlinarith [abs_nonneg (u2 : ℝ)]
    calc _ ≤ |(u1 : ℝ) * (Real.log (c : ℝ) - Λ)| + |(u2 : ℝ) * Real.log 2| := abs_sub _ _
      _ ≤ _ := add_le_add e1 e2
  have hlhs : (i : ℝ) / 25 ≤ |(i : ℝ) * ((u1 : ℝ) * Real.log 3 + (u3 : ℝ) * Real.log 2)| := by
    rw [abs_mul, abs_of_pos hi0]
    nlinarith
  rw [key] at hlhs
  have hbig := BB6KitEx.big n hn
  have hbigR : (2:ℝ) ^ 26 * (n : ℝ) ^ 2 < (i : ℝ) := by
    have : 2 ^ 26 * n ^ 2 < i := lt_of_lt_of_le hbig hi
    exact_mod_cast this
  have hn60 : (60:ℝ) ≤ n := by exact_mod_cast hn
  have hnsq : 60 * (n:ℝ) ≤ (n:ℝ) ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hn60 (by positivity)
  generalize |(u1 : ℝ) * (Real.log (c : ℝ) - Λ) - (u2 : ℝ) * Real.log 2| = A at hlhs hrhs
  generalize (n : ℝ) ^ 2 = N2 at hnsq hbigR hr
  generalize (i : ℝ) = I at hlhs hbigR
  generalize (n : ℝ) = N1 at hnsq hn60 hrhs
  linarith only [hlhs, hrhs, hbigR, hnsq, hn60, hr]
