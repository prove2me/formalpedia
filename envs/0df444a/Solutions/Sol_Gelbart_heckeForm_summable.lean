-- Prove2me | solution 1 for Gelbart.heckeForm_summable
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T23:41:26.446693+00:00
-- url     : https://prove2.me/submissions/81b7b3b1-3b1a-4adb-9c45-8cff239e68a7

import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_Gelbart_hecke_series

namespace Gelbart

theorem heckeForm_summable
    (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * z / h) := by
  obtain ⟨K, hK⟩ := hgrowth
  have hK0 : 0 ≤ K := by
    have hh := hK 1 (by omega)
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at hh
    exact (norm_nonneg _).trans hh
  let r : ℝ := 2 * Real.pi * z.im / h
  have hr : 0 < r := div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hz) hh
  have hm := (Real.summable_pow_mul_exp_neg_nat_mul (Nat.ceil c) hr).mul_left K
  apply hm.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n:ℝ)^c ≤ (n:ℝ)^(Nat.ceil c) := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hnR (Nat.le_ceil c)
  have ha : ‖a n‖ ≤ K * (n:ℝ)^(Nat.ceil c) :=
    (hK n hn).trans (mul_le_mul_of_nonneg_left hp hK0)
  have hre : (2 * ↑Real.pi * Complex.I * ↑n * z / ↑h).re = -r*n := by
    simp only [Complex.div_ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im]
    dsimp [r]
    ring
  rw [norm_mul, Complex.norm_exp, hre]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ha (Real.exp_nonneg (-r*n))

end Gelbart

theorem solution
    (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : Gelbart.HeckeCoeffGrowth a c) {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * z / h) :=
  Gelbart.heckeForm_summable a c h hc hh hgrowth hz

#print axioms Gelbart.heckeForm_summable
#print axioms solution
