-- Prove2me | solution 1 for FastFashion.Approx.tangent_slopes_pos_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:49:25.795434+00:00
-- url     : https://prove2.me/submissions/c33387e1-a431-4b82-986f-b1013886adee

import Mathlib
import Definitions.Def_FastFashion_Approx_Tangents

set_option autoImplicit false
open FastFashion.Approx

theorem lg_succ (k : ℕ) (b : ℝ) :
    lowerGamma (k + 2) b = (k + 1) * lowerGamma (k + 1) b - b ^ (k + 1) * Real.exp (-b) := by
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 1 - 1 = k := by omega
  unfold lowerGamma
  rw [e1, e2]
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) b, HasDerivAt (fun x : ℝ => x ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
    intro x _
    simpa using hasDerivAt_pow (k + 1) x
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) b, HasDerivAt (fun x : ℝ => -Real.exp (-x)) (Real.exp (-x)) x := by
    intro x _
    have := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    exact this.neg.congr_deriv (by ring)
  have hu' : IntervalIntegrable (fun x : ℝ => ((k + 1 : ℕ) : ℝ) * x ^ k) MeasureTheory.volume 0 b :=
    (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x : ℝ => Real.exp (-x)) MeasureTheory.volume 0 b :=
    (Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _
  have := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [this]
  have h3 : ∫ x in (0:ℝ)..b, ((k + 1 : ℕ) : ℝ) * x ^ k * -Real.exp (-x)
      = -(((k + 1 : ℕ) : ℝ) * ∫ x in (0:ℝ)..b, x ^ k * Real.exp (-x)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  rw [h3]
  simp
  ring

theorem lg_pos (k : ℕ) (b : ℝ) (hb : 0 < b) : 0 < lowerGamma (k + 1) b := by
  unfold lowerGamma
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (((continuous_pow _).mul (Real.continuous_exp.comp continuous_neg))).intervalIntegrable _ _
  · intro x hx
    exact mul_pos (pow_pos hx.1 _) (Real.exp_pos _)
  · exact hb

theorem solution (lam T : ℝ) (hlam : 0 < lam) (hT : 0 < T) (k : ℕ) :
    0 < a lam T k ∧ a lam T (k + 1) < a lam T k := by
  have hb : 0 < lam * T := mul_pos hlam hT
  have hf : (0:ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  constructor
  · unfold a
    exact div_pos (lg_pos k _ hb) (mul_pos hlam hf)
  · unfold a
    have hrec := lg_succ k (lam * T)
    have e : k + 1 + 1 = k + 2 := rfl
    rw [e, hrec]
    have hfs : (Nat.factorial (k + 1) : ℝ) = (k + 1) * Nat.factorial k := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfs]
    have hpos : 0 < (lam * T) ^ (k + 1) * Real.exp (-(lam * T)) :=
      mul_pos (pow_pos hb _) (Real.exp_pos _)
    have hk : (0:ℝ) < (k + 1) := by positivity
    rw [div_lt_div_iff₀ (by positivity) (mul_pos hlam hf)]
    nlinarith [mul_pos hpos (mul_pos hlam hf)]
