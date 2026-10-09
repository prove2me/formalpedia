-- Prove2me | solution 1 for GaussianMatrix.inv_chi_square_Lq_bound
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T05:01:33.310157+00:00
-- url     : https://prove2.me/submissions/8038e577-fe32-42fc-9d98-387c6dd4e3ba

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_chi_square_neg_moment

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open Real

/-- `Γ(x + 1/2) ≤ Γ(x) √x` for `x > 0` (log-convexity of `Γ`). -/
lemma icl_Gamma_add_half_le {x : ℝ} (hx : 0 < x) :
    Gamma (x + 1 / 2) ≤ Gamma x * √x := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx (by linarith : 0 < x + 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hG : 0 < Gamma x := Gamma_pos_of_pos hx
  rw [show 1 / 2 * x + 1 / 2 * (x + 1) = x + 1 / 2 by ring, Gamma_add_one hx.ne',
    ← Real.mul_rpow hG.le (by positivity), ← Real.sqrt_eq_rpow,
    show Gamma x * (x * Gamma x) = Gamma x ^ 2 * x by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hG.le] at h
  exact h

/-- `exp(n) * 3 < 2 * 3^n` for `n ≥ 5`. -/
lemma icl_exp_lt {n : ℕ} (hn : 5 ≤ n) : Real.exp 1 ^ n * 3 < 2 * 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have he3 : Real.exp 1 ≤ 3 := by linarith
  have h5 : Real.exp 1 ^ 5 * 3 < 2 * 3 ^ 5 := by
    have : Real.exp 1 ^ 5 < 2.7182818286 ^ 5 := pow_lt_pow_left₀ he he0.le (by norm_num)
    have : (2.7182818286 : ℝ) ^ 5 * 3 < 2 * 3 ^ 5 := by norm_num
    nlinarith
  have hm : Real.exp 1 ^ m ≤ 3 ^ m := pow_le_pow_left₀ he0.le he3 m
  rw [pow_add, pow_add]
  have : 0 < Real.exp 1 ^ 5 := by positivity
  have : (0 : ℝ) < 3 ^ m := by positivity
  nlinarith

/-- The Gamma-function inequality behind HMT Lemma A.10:
`√π / (2^q Γ(n/2)) < (3/n)^q` for `q = (n-1)/2`, `n ≥ 5`. -/
lemma icl_gamma_ineq {n : ℕ} (hn : 5 ≤ n) :
    √π / (2 ^ (((n : ℝ) - 1) / 2) * Gamma ((n : ℝ) / 2)) < (3 / (n : ℝ)) ^ (((n : ℝ) - 1) / 2) := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set x : ℝ := (n : ℝ) / 2 with hx
  have hx0 : 0 < x := by positivity
  set q : ℝ := ((n : ℝ) - 1) / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  set G := Gamma x with hGdef
  have hG : 0 < G := Gamma_pos_of_pos hx0
  set s := √x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  set sp := √π with hsp
  have hsp0 : 0 < sp := Real.sqrt_pos.mpr Real.pi_pos
  have hspsq : sp ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  -- F1, F2
  have F1 : Gamma (x + 1 / 2) ≤ G * s := icl_Gamma_add_half_le hx0
  have F2 : G * Gamma (x + 1 / 2) = Gamma n * (2 : ℝ) ^ (1 - (n : ℝ)) * sp := by
    rw [hGdef, Real.Gamma_mul_Gamma_add_half, hx, show 2 * ((n : ℝ) / 2) = n by ring]
  -- F3 : n Γ(n) = n!
  have F3 : (n : ℝ) * Gamma n = (n.factorial : ℝ) := by
    rw [← Real.Gamma_add_one hn0.ne', Real.Gamma_nat_eq_factorial]
  -- F4, F5 : Stirling
  have F4 := Stirling.le_factorial_stirling n
  have F5 : √(2 * π * n) = 2 * sp * s := by
    rw [show 2 * π * (n : ℝ) = 2 ^ 2 * π * x by rw [hx]; ring, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have F6 := icl_exp_lt hn
  have F7 : (2 : ℝ) ^ (1 - (n : ℝ)) * 2 ^ n = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    norm_num
  have hen : Real.exp 1 ^ n > 0 := by positivity
  have hdivpow : ((n : ℝ) / Real.exp 1) ^ n = (n : ℝ) ^ n / Real.exp 1 ^ n := div_pow _ _ _
  -- chain
  have h1 : G * Gamma (x + 1 / 2) ≤ G ^ 2 * s := by
    have := mul_le_mul_of_nonneg_left F1 hG.le; nlinarith
  have h3 : (n.factorial : ℝ) * sp * 2 ≤ n * 2 ^ n * G ^ 2 * s := by
    have h2 : Gamma n * (2 : ℝ) ^ (1 - (n : ℝ)) * sp ≤ G ^ 2 * s := F2 ▸ h1
    have hpos : (0 : ℝ) ≤ n * 2 ^ n := by positivity
    have := mul_le_mul_of_nonneg_left h2 hpos
    calc (n.factorial : ℝ) * sp * 2 = (n * Gamma n) * ((2 : ℝ) ^ (1 - (n : ℝ)) * 2 ^ n) * sp := by
          rw [F3, F7]; ring
      _ = n * 2 ^ n * (Gamma n * (2 : ℝ) ^ (1 - (n : ℝ)) * sp) := by ring
      _ ≤ n * 2 ^ n * (G ^ 2 * s) := this
      _ = n * 2 ^ n * G ^ 2 * s := by ring
  have h4 : 2 * sp * s * ((n : ℝ) ^ n / Real.exp 1 ^ n) ≤ n.factorial := by
    rw [← F5, ← hdivpow]; exact F4
  have h5 : 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * s ≤ n * 2 ^ n * G ^ 2 * s := by
    calc 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * s
        = (2 * sp * s * ((n : ℝ) ^ n / Real.exp 1 ^ n)) * sp * 2 := by rw [← hspsq]; ring
      _ ≤ (n.factorial : ℝ) * sp * 2 := by gcongr
      _ ≤ _ := h3
  have h6 : 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) ≤ n * 2 ^ n * G ^ 2 :=
    le_of_mul_le_mul_right h5 hs0
  -- key : 6 π n^n < n 6^n G²
  have hnn : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  have key : 6 * π * (n : ℝ) ^ n < n * 6 ^ n * G ^ 2 := by
    have h7 : 6 * π * (n : ℝ) ^ n < 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * 3 ^ n := by
      rw [show 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * 3 ^ n
        = (π * (n : ℝ) ^ n) * (2 * (2 * 3 ^ n)) / Real.exp 1 ^ n by ring]
      rw [lt_div_iff₀ hen]
      have hpn : 0 < π * (n : ℝ) ^ n := by positivity
      nlinarith
    calc 6 * π * (n : ℝ) ^ n < 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * 3 ^ n := h7
      _ ≤ n * 2 ^ n * G ^ 2 * 3 ^ n := by gcongr
      _ = n * 6 ^ n * G ^ 2 := by
        rw [show (6 : ℝ) ^ n = 2 ^ n * 3 ^ n by rw [← mul_pow]; norm_num]; ring
  -- convert key to the goal
  have h2q : 2 * q = (n : ℝ) - 1 := by rw [hq]; ring
  have hsq : ∀ a : ℝ, 0 < a → (a ^ q) ^ 2 = a ^ n / a := by
    intro a ha
    rw [← Real.rpow_natCast (a ^ q) 2, ← Real.rpow_mul ha.le, show q * ((2 : ℕ) : ℝ) = 2 * q by
      push_cast; ring, h2q, Real.rpow_sub_one ha.ne', Real.rpow_natCast a n]
  have hA : sp * (n : ℝ) ^ q < (6 : ℝ) ^ q * G := by
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    rw [mul_pow, mul_pow, hspsq, hsq _ hn0, hsq 6 (by norm_num)]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have : π * ((n : ℝ) ^ n * (n : ℝ)⁻¹) = (6 * π * (n : ℝ) ^ n) * (6 * (n : ℝ))⁻¹ := by
      field_simp
    rw [this, show (6 : ℝ) ^ n * 6⁻¹ * G ^ 2 = (n * 6 ^ n * G ^ 2) * (6 * (n : ℝ))⁻¹ by field_simp]
    exact mul_lt_mul_of_pos_right key (by positivity)
  have h2q0 : (0 : ℝ) < 2 ^ q := by positivity
  rw [div_lt_iff₀ (by positivity), Real.div_rpow (by norm_num) hn0.le]
  rw [show (3 : ℝ) ^ q / (n : ℝ) ^ q * (2 ^ q * G) = ((2 : ℝ) ^ q * 3 ^ q) * G / (n : ℝ) ^ q by
    ring, ← Real.mul_rpow (by norm_num) (by norm_num), lt_div_iff₀ (by positivity)]
  norm_num
  linarith

end GaussianMatrix

open GaussianMatrix

theorem solution {d : ℕ} (hd : 5 ≤ d) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2))
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      < (3 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hint, hval⟩ := chi_square_neg_moment (d := d) (((d : ℝ) - 1) / 2) (by linarith)
    (by linarith)
  refine ⟨hint, ?_⟩
  rw [hval, show (d : ℝ) / 2 - ((d : ℝ) - 1) / 2 = 1 / 2 by ring, Real.Gamma_one_half_eq]
  exact icl_gamma_ineq hd
