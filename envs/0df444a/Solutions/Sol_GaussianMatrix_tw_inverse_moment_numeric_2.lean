-- Prove2me | solution 2 for GaussianMatrix.tw_inverse_moment_numeric
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:04:18.515986+00:00
-- url     : https://prove2.me/submissions/53d04367-3695-4d0d-921b-8f8dc6ce3195

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- The integer inequality `(2p+1)^(2p+2) ≤ 46^(2p)` for `1 ≤ p ≤ 18`. -/
lemma twnum_int_check {p : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18) :
    (2 * p + 1) ^ (2 * p + 2) ≤ 46 ^ (2 * p) := by
  interval_cases p <;> norm_num

/-- `46 ≤ 2π e²`. -/
lemma twnum_46_le : (46 : ℝ) ≤ 2 * Real.pi * Real.exp 1 ^ 2 := by
  have he := Real.exp_one_gt_d9
  have hpi := Real.pi_gt_d2
  nlinarith

/-- `(c+2) log(c+1) ≤ c (log (2π) + 2)` for `c = 2p`, `1 ≤ p ≤ 18`. -/
lemma twnum_S4 {p : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18) :
    (2 * (p : ℝ) + 2) * Real.log (2 * p + 1)
      ≤ 2 * (p : ℝ) * (Real.log (2 * Real.pi) + 2) := by
  have hint : ((2 * p + 1 : ℕ) : ℝ) ^ (2 * p + 2) ≤ ((46 : ℕ) : ℝ) ^ (2 * p) := by
    exact_mod_cast twnum_int_check hp hp18
  push_cast at hint
  have h46 : (46 : ℝ) ^ (2 * p) ≤ (2 * Real.pi * Real.exp 1 ^ 2) ^ (2 * p) :=
    pow_le_pow_left₀ (by norm_num) twnum_46_le _
  have hpos : (0 : ℝ) < (2 * p + 1) ^ (2 * p + 2) := by positivity
  have hlog := Real.log_le_log hpos (hint.trans h46)
  rw [Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_exp] at hlog
  push_cast at hlog
  linarith

end GaussianMatrix

open GaussianMatrix

theorem solution {p x : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18) (hx : 2 * p ≤ x) :
    (1 + 2 * (p : ℝ) / ((x : ℝ) + 1 - 2 * p))
        * (1 / Real.Gamma ((x : ℝ) + 2)) ^ (2 * (p : ℝ) / ((x : ℝ) + 1))
      ≤ (Real.exp 1 / x) ^ (2 * p) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hxR : 2 * (p : ℝ) ≤ x := by exact_mod_cast hx
  set X : ℝ := (x : ℝ) with hX
  set c : ℝ := 2 * (p : ℝ) with hc
  set n : ℝ := X + 1 with hn
  have hc0 : 0 < c := by rw [hc]; linarith
  have hX0 : 0 < X := by linarith
  have hn0 : 0 < n := by linarith
  have hnc : 0 < n - c := by rw [hn]; linarith
  -- the factorial
  have hG : Real.Gamma (X + 2) = ((x + 1).factorial : ℝ) := by
    have h2 : ((x + 1 : ℕ) : ℝ) + 1 = X + 2 := by rw [hX]; push_cast; ring
    rw [← Real.Gamma_nat_eq_factorial, h2]
  set F : ℝ := ((x + 1).factorial : ℝ) with hF
  have hF0 : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  rw [hG]
  set a : ℝ := 1 + c / (X + 1 - c) with ha
  have ha' : a = n / (n - c) := by
    have hd : X + 1 - c ≠ 0 := by linarith
    rw [ha, hn]; field_simp; ring
  have ha0 : 0 < a := by rw [ha']; positivity
  have hL : 0 < a * (1 / F) ^ (c / n) := by positivity
  have hR : 0 < (Real.exp 1 / X) ^ (2 * p) := by positivity
  have hF1 : (0 : ℝ) < 1 / F := by positivity
  have hrp : (0 : ℝ) < (1 / F) ^ (c / n) := Real.rpow_pos_of_pos hF1 _
  rw [← Real.log_le_log_iff hL hR, Real.log_mul ha0.ne' hrp.ne',
    Real.log_rpow hF1, Real.log_pow, Real.log_div (Real.exp_pos 1).ne' hX0.ne',
    Real.log_exp, one_div, Real.log_inv]
  -- S1: Stirling
  have hS1 : (1 / 2) * Real.log (2 * Real.pi * n) + n * Real.log n - n ≤ Real.log F := by
    have h := Stirling.le_factorial_stirling (x + 1)
    have hcast : ((x + 1 : ℕ) : ℝ) = n := by rw [hn, hX]; push_cast; ring
    rw [hcast] at h
    have hpos : 0 < Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ (x + 1) := by positivity
    have hl := Real.log_le_log hpos h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
      Real.log_pow, Real.log_div hn0.ne' (Real.exp_pos 1).ne', Real.log_exp] at hl
    have hcast2 : ((x + 1 : ℕ) : ℝ) = n := hcast
    rw [hcast2] at hl
    linarith
  -- S2: concavity of log
  have hS2 : n * (Real.log n - Real.log (n - c)) ≤ (c + 1) * Real.log (c + 1) := by
    have hconc := strictConcaveOn_log_Ioi.concaveOn
    have hb0 : 0 ≤ (c + 1) / n := by positivity
    have hb1 : (c + 1) / n ≤ 1 := by rw [div_le_one hn0]; rw [hn]; linarith
    have h : (1 - (c + 1) / n) • Real.log 1 + ((c + 1) / n) • Real.log (1 / (c + 1))
        ≤ Real.log ((1 - (c + 1) / n) • (1 : ℝ) + ((c + 1) / n) • (1 / (c + 1))) :=
      hconc.2 (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 (by positivity)) (by linarith) hb0
        (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at h
    have hpt : 1 - (c + 1) / n + (c + 1) / n * (1 / (c + 1)) = (n - c) / n := by
      field_simp; ring
    rw [hpt, Real.log_div hnc.ne' hn0.ne', one_div, Real.log_inv] at h
    have h2 : n * ((c + 1) / n * -Real.log (c + 1)) ≤ n * (Real.log (n - c) - Real.log n) :=
      mul_le_mul_of_nonneg_left h hn0.le
    have h3 : n * ((c + 1) / n * -Real.log (c + 1)) = -((c + 1) * Real.log (c + 1)) := by
      field_simp
    linarith
  -- S3: `n log((n-1)/n) ≤ -1`
  have hS3 : n * Real.log X - n * Real.log n ≤ -1 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := n / X) (by positivity)
    rw [Real.log_div hn0.ne' hX0.ne', inv_div] at h
    have h1 : 1 - X / n = 1 / n := by rw [hn]; field_simp; ring
    rw [h1] at h
    have h2 : n * (1 / n) ≤ n * (Real.log n - Real.log X) := mul_le_mul_of_nonneg_left h hn0.le
    rw [mul_one_div_cancel hn0.ne'] at h2
    linarith
  -- S4: the numerical check
  have hS4 : (c + 2) * Real.log (c + 1) ≤ c * (Real.log (2 * Real.pi) + 2) := by
    have := twnum_S4 hp hp18
    rw [hc]; linarith
  -- S5: monotonicity of log
  have hS5 : Real.log (2 * Real.pi * (c + 1)) ≤ Real.log (2 * Real.pi * n) :=
    Real.log_le_log (by positivity) (by
      have : c + 1 ≤ n := by rw [hn]; linarith
      nlinarith [Real.pi_pos])
  have hS5' : Real.log (2 * Real.pi * (c + 1)) = Real.log (2 * Real.pi) + Real.log (c + 1) :=
    Real.log_mul (by positivity) (by positivity)
  have hla : Real.log a = Real.log n - Real.log (n - c) := by
    rw [ha', Real.log_div hn0.ne' hnc.ne']
  rw [hla]
  -- combine: multiply the goal by `n > 0`
  have hpc : ((2 * p : ℕ) : ℝ) = c := by rw [hc]; push_cast; ring
  rw [hpc]
  have key : n * (Real.log n - Real.log (n - c)) - c * Real.log F
      ≤ n * (c * (1 - Real.log X)) := by
    have e1 : c * ((1 / 2) * Real.log (2 * Real.pi * n) + n * Real.log n - n)
        ≤ c * Real.log F := mul_le_mul_of_nonneg_left hS1 hc0.le
    have e3 : c * (n * Real.log X - n * Real.log n) ≤ c * (-1) :=
      mul_le_mul_of_nonneg_left hS3 hc0.le
    have e5 : c * Real.log (2 * Real.pi * (c + 1)) ≤ c * Real.log (2 * Real.pi * n) :=
      mul_le_mul_of_nonneg_left hS5 hc0.le
    rw [hS5'] at e5
    nlinarith
  have hfin : n * (Real.log n - Real.log (n - c) + c / n * -Real.log F)
      ≤ n * (c * (1 - Real.log X)) := by
    have : n * (Real.log n - Real.log (n - c) + c / n * -Real.log F)
        = n * (Real.log n - Real.log (n - c)) - c * Real.log F := by field_simp; ring
    rw [this]; exact key
  exact le_of_mul_le_mul_left hfin hn0
