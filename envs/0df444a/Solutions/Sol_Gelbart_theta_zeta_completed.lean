-- Prove2me | solution 1 for Gelbart.theta_zeta_completed
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T23:20:49.319192+00:00
-- url     : https://prove2.me/submissions/ca94ba80-7d07-417f-9ca2-67e90e397f2d

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Gelbart_hecke_series
import Definitions.Def_Gelbart_theta_coeff

namespace Gelbart

private theorem theta_lseries (s : ℂ) (hs : 1 / 2 < s.re) :
    LSeries thetaCoeff s = 2 * riemannZeta (2 * s) := by
  have hs2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hs20 : 2 * s ≠ 0 := Complex.ne_zero_of_one_lt_re hs2
  have hinj : Function.Injective (fun n : ℕ => n * n) := by
    intro a b hab
    simpa only [Nat.sqrt_eq] using congrArg Nat.sqrt hab
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => k * k), LSeries.term thetaCoeff s n = 0 := by
    intro n hn
    have hnsq : ¬ Nat.sqrt n * Nat.sqrt n = n := by
      intro he
      exact hn ⟨Nat.sqrt n, he⟩
    simp [LSeries.term, thetaCoeff, hnsq]
  have hsupp : Function.support (LSeries.term thetaCoeff s) ⊆
      Set.range (fun k : ℕ => k * k) := by
    intro n hn
    by_contra h
    exact hn (hzero n h)
  have hreindex := hinj.tsum_eq hsupp
  change (∑' n : ℕ, LSeries.term thetaCoeff s n) = _
  rw [← hreindex, zeta_eq_tsum_one_div_nat_cpow hs2, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, hs20, Complex.zero_cpow]
  · rw [LSeries.term_of_ne_zero (mul_ne_zero hn hn)]
    have hcoeff : thetaCoeff (n * n) = 2 := by
      simp [thetaCoeff, Nat.sqrt_eq, hn]
    rw [hcoeff]
    have hpow : ((n * n : ℕ) : ℂ) ^ s = (n : ℂ) ^ (2 * s) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, pow_two] using
        (Complex.natCast_cpow_natCast_mul n 2 s).symm
    rw [hpow]
    ring

theorem theta_zeta_completed (s : ℂ) (hs : 1 / 2 < s.re) :
    heckeCompletedLSeries thetaCoeff 2 s
      = 2 * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s) := by
  unfold heckeCompletedLSeries
  rw [theta_lseries s hs]
  have hpi : (2 * Real.pi / 2 : ℂ) = Real.pi := by ring
  norm_num only [Complex.ofReal_ofNat]
  rw [hpi]
  ring

end Gelbart

theorem solution (s : ℂ) (hs : 1 / 2 < s.re) :
    Gelbart.heckeCompletedLSeries Gelbart.thetaCoeff 2 s
      = 2 * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s) :=
  Gelbart.theta_zeta_completed s hs

#print axioms Gelbart.theta_zeta_completed
#print axioms solution
