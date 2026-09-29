-- Prove2me | solution 1 for FourExp.extrapolation_numbers
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-27T08:09:58.306107+00:00
-- url     : https://prove2.me/submissions/4a95e926-e2e0-42c8-9364-a4d710288923

import Mathlib

/-!
# The numerical inequality of the extrapolation step

Put `L = log N`, `q = √L`, `A = N² q` and `U = N³ q`; the hypothesis on `N` gives `N ≥ 416`, so
`L ≥ 1` and `A ≤ U`. The zero factor is small: `t₁ t₂ S ≥ N⁴ / (8 q)` and `log (N - 1) ≥ L / 2`,
so `(N - 1)^(-t₁ t₂ S) ≤ e^(-N U / 16)`. Every other factor is at most an exponential:
`s! ≤ S^S ≤ e^(2 A)`, `2 ≤ e`, `S (2N)² ≤ 4 N⁴ ≤ e^(7 U)`, the factor `e^(κ A)`,
`(Y A)^S ≤ e^((log Y + 3) A)` and `e^(2 N X Y A) = e^(2 X Y U)`. With `A ≤ U` and `U ≥ 1` the
total exponent is at most `-N U / 16 + (13 + κ + log Y + 2 X Y) U ≤ -N U / 32 = -N⁴ q / 32`.
-/

theorem solution (X Y κ : ℝ) (hX : 0 ≤ X) (hY : 1 ≤ Y) (hκ : 0 ≤ κ)
    (N S t₁ t₂ s : ℕ) (hbig : 32 * (13 + κ + Real.log Y + 2 * X * Y) ≤ N) (hs : s ≤ S)
    (hSu : (S : ℝ) * Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2)
    (hSl : (N : ℝ) ^ 2 ≤ 2 * (S * Real.sqrt (Real.log N)))
    (h₁ : (N : ℝ) ≤ 2 * (t₁ * Real.sqrt (Real.log N)))
    (h₂ : (N : ℝ) * Real.sqrt (Real.log N) ≤ 2 * t₂) :
    (s.factorial : ℝ) * 2 * (1 / ((N : ℝ) - 1)) ^ (t₁ * t₂ * S) *
        (S * (2 * N) * (2 * N) * Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) *
          (Y * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) ^ S *
          Real.exp (2 * N * X * (Y * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N)))))
      ≤ Real.exp (-((N : ℝ) ^ 4 * Real.sqrt (Real.log N) / 32)) := by
  -- the scale: `N ≥ 416`, `L = log N ≥ 1`, `q = √L`, `A = N² q`, `U = N³ q`
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hXY : 0 ≤ 2 * X * Y := by positivity
  have hNr : (416 : ℝ) ≤ N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]; linarith [Real.exp_one_lt_d9]
  have hLN : Real.log N ≤ N := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)]
  have hLN1 : Real.log N / 2 ≤ Real.log ((N : ℝ) - 1) := by
    have := Real.log_le_log (by positivity) (by nlinarith : (N : ℝ) ≤ ((N : ℝ) - 1) ^ 2)
    rw [Real.log_pow] at this; push_cast at this; linarith
  set L := Real.log N with hLdef
  set q := Real.sqrt L with hqdef
  have hq1 : 1 ≤ q := Real.one_le_sqrt.2 hL1
  have hqq : q * q = L := Real.mul_self_sqrt (by linarith)
  have hqN : q ≤ N := by linarith [le_mul_of_one_le_left (by linarith : (0 : ℝ) ≤ q) hq1]
  set A := (N : ℝ) ^ 2 * q with hA
  set U := (N : ℝ) ^ 3 * q with hU
  have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hAU : A ≤ U := mul_le_mul_of_nonneg_right hN2 (by linarith)
  have hN2A : (N : ℝ) ^ 2 ≤ A := le_mul_of_one_le_right (by positivity) hq1
  have hLU : L ≤ U := hLN.trans (by nlinarith)
  have hU1 : 1 ≤ U := hL1.trans hLU
  have hS0 : (1 : ℝ) ≤ S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · rw [h, Nat.cast_zero, zero_mul, mul_zero] at hSl; nlinarith
    · exact_mod_cast h
  have hS1 : 1 ≤ S := by exact_mod_cast hS0
  have hSN : (S : ℝ) ≤ N ^ 2 := (le_mul_of_one_le_right (by linarith) hq1).trans hSu
  have hSL : (S : ℝ) * L ≤ q * N ^ 2 := by
    rw [← hqq]; linarith [mul_le_mul_of_nonneg_left hSu (by linarith : (0 : ℝ) ≤ q)]
  -- (1) `s! ≤ S ^ S ≤ exp (2 A)`
  have e1 : (s.factorial : ℝ) ≤ Real.exp (2 * A) := by
    have hnat : s.factorial ≤ S ^ S :=
      (Nat.factorial_le_pow s).trans ((Nat.pow_le_pow_left hs s).trans (Nat.pow_le_pow_right hS1 hs))
    refine (show (s.factorial : ℝ) ≤ (S : ℝ) ^ S by exact_mod_cast hnat).trans ?_
    rw [← Real.exp_log (by linarith : (0 : ℝ) < S), ← Real.exp_nat_mul]
    have := Real.log_le_log (by linarith) hSN
    rw [Real.log_pow] at this; push_cast at this
    refine Real.exp_le_exp.2 ?_
    linarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ S)]
  -- (2) the zero factor: `t₁ t₂ S ≥ N⁴ / (8 q)` and `log (N - 1) ≥ q² / 2`
  have e2 : (1 / ((N : ℝ) - 1)) ^ (t₁ * t₂ * S) ≤ Real.exp (-(N * U / 16)) := by
    rw [one_div, ← Real.exp_log (by linarith : (0 : ℝ) < N - 1), ← Real.exp_neg, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have f1 : (N : ℝ) * (N * q) ≤ (2 * (t₁ * q)) * (2 * t₂) :=
      mul_le_mul h₁ h₂ (by positivity) (by positivity)
    have f2 := mul_le_mul f1 hSl (by positivity) (by positivity)
    have g := mul_le_mul_of_nonneg_left hLN1 (Nat.cast_nonneg (α := ℝ) (t₁ * t₂ * S))
    push_cast at g ⊢
    rw [hU]; linear_combination g + f2 / 16 + ((t₁ : ℝ) * t₂ * S / 2) * hqq
  -- (3) the remaining factors, each at most `exp (const * U)`
  have e3 : (S : ℝ) * (2 * N) * (2 * N) ≤ Real.exp (7 * U) := by
    have h4 : (S : ℝ) * (2 * N) * (2 * N) ≤ 4 * (N : ℝ) ^ 4 := by
      linear_combination (4 * (N : ℝ) ^ 2) * hSN
    refine h4.trans ?_
    rw [show (4 : ℝ) * (N : ℝ) ^ 4 = Real.exp (Real.log 4 + 4 * L) by
      rw [Real.exp_add, Real.exp_log (by norm_num), hLdef, ← Real.log_rpow (by positivity),
        Real.exp_log (by positivity)]; norm_cast]
    have : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact Real.exp_le_exp.2 (by linarith)
  have e4 : (Y * A) ^ S ≤ Real.exp ((Real.log Y + 3) * A) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < Y * A), ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have hA3 : Real.log A ≤ 3 * L := by
      have := Real.log_le_log (by positivity) (show A ≤ (N : ℝ) ^ 3 by
        rw [hA]; exact (mul_le_mul_of_nonneg_left hqN (by positivity)).trans_eq (by ring))
      rwa [Real.log_pow] at this
    rw [Real.log_mul (by positivity) (by positivity)]
    have f1 := mul_le_mul_of_nonneg_right (hSN.trans hN2A) hlogY
    have f2 := mul_le_mul_of_nonneg_left hA3 (by linarith : (0 : ℝ) ≤ S)
    rw [hA] at f1 ⊢
    linear_combination f1 + f2 + 3 * hSL
  have e5 : 2 * N * X * (Y * A) = 2 * X * Y * U := by rw [hA, hU]; ring
  calc _ ≤ Real.exp (2 * A) * Real.exp 1 * Real.exp (-(N * U / 16)) *
        (Real.exp (7 * U) * Real.exp (κ * A) * Real.exp ((Real.log Y + 3) * A) *
          Real.exp (2 * X * Y * U)) := by
        rw [← e5]
        gcongr
        · exact pow_nonneg (div_nonneg zero_le_one (by linarith)) _
        · linarith [Real.add_one_le_exp 1]
    _ = Real.exp (2 * A + 1 + -(N * U / 16) + (7 * U + κ * A + (Real.log Y + 3) * A + 2 * X * Y * U)) := by
        simp only [Real.exp_add]
    _ ≤ Real.exp (-((N : ℝ) ^ 4 * q / 32)) := by
        refine Real.exp_le_exp.2 ?_
        rw [show (N : ℝ) ^ 4 * q = N * U by rw [hU]; ring]
        have k1 := mul_le_mul_of_nonneg_right hbig (by linarith : (0 : ℝ) ≤ U)
        have k2 := mul_le_mul_of_nonneg_left hAU (by linarith : (0 : ℝ) ≤ 5 + κ + Real.log Y)
        linear_combination k1 / 32 + k2 + hU1

#print axioms solution
