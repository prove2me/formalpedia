-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.073071+00:00
-- url     : https://prove2.me/submissions/fab2c860-078c-4418-8fe9-82d4f93bb9f6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_one_le_log_nat
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_exp_neg_le_div_pow_four

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
namespace Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
theorem _root_.solution (a : ℕ → ℂ) (Q C₁ c₁ : ℝ) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hQ : 0 < Q)
    (hL : 1 ≤ Real.log Q)
    (H1 : ∀ u : ℝ, 2 ≤ u → ‖psum a u‖ ≤
          C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2))
    (H2 : ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u →
          ‖psum a u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u)))
    (n : ℕ) (hn : 3 ≤ n) :
    ‖∑ k ∈ Icc 1 n, a k‖ ≤
      n * (C₁ * ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) +
        (C₁ * (4 * Real.log Q ^ 8 * Real.exp (-Real.log Q) +
          384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * Real.log Q)))) * (1 / Real.log (n : ℝ) ^ 2)) := by
  have hps : psum a (n : ℝ) = ∑ k ∈ Icc 1 n, a k := by simp [psum]
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n := by linarith
  have hlog := one_le_log_nat n hn
  set L := Real.log Q with hLdef
  set t := Real.log (n : ℝ) with ht
  have hw : 0 ≤ (n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2 := by positivity
  have hE1 : 0 ≤ 4 * L ^ 8 * Real.exp (-L) := by positivity
  have hE2 : 0 ≤ 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L)) := by positivity
  have ht2 : 0 < t ^ 2 := by positivity
  rw [← hps]
  by_cases h : Real.exp (L ^ 2) ≤ n
  · refine (H2 n h).trans ?_
    rw [← ht]
    set s := Real.sqrt t with hs
    have hss : s ^ 2 = t := Real.sq_sqrt (by linarith)
    have hLt : L ^ 2 ≤ t := by rw [ht, Real.le_log_iff_exp_le hn']; exact h
    have hLs : L ≤ s := by rw [hs, Real.le_sqrt' (by linarith)]; exact hLt
    have hs0 : 0 < s := by linarith
    have e1 : Real.exp (-c₁ * s) = Real.exp (-(c₁ / 2 * s)) * Real.exp (-(c₁ / 2 * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(c₁ / 2 * s)) ≤ Real.exp (-(c₁ / 2 * L)) := by
      apply Real.exp_le_exp.mpr
      have : c₁ / 2 * L ≤ c₁ / 2 * s := mul_le_mul_of_nonneg_left hLs (by positivity)
      linarith
    have e3 : Real.exp (-(c₁ / 2 * s)) ≤ 24 / (c₁ / 2 * s) ^ 4 := exp_neg_le_div_pow_four _ (by positivity)
    have e4 : 24 / (c₁ / 2 * s) ^ 4 = 384 / c₁ ^ 4 * (1 / t ^ 2) := by
      rw [← hss]; field_simp; ring
    have e5 : Real.exp (-c₁ * s) ≤ 384 / c₁ ^ 4 * (1 / t ^ 2) * Real.exp (-(c₁ / 2 * L)) := by
      rw [e1, ← e4]
      exact mul_le_mul e3 e2 (Real.exp_pos _).le (by positivity)
    have e6 : 0 ≤ 4 * L ^ 8 * Real.exp (-L) * (1 / t ^ 2) := by positivity
    have e7 : Real.exp (-c₁ * s) ≤ ((n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2) +
        (4 * L ^ 8 * Real.exp (-L) + 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L))) * (1 / t ^ 2) := by
      nlinarith
    have e8 := mul_le_mul_of_nonneg_left e7 (mul_nonneg hC₁.le hn'.le)
    refine e8.trans (le_of_eq ?_)
    ring
  · rw [not_le] at h
    have htL : t < L ^ 2 := by rw [ht, Real.log_lt_iff_lt_exp hn']; exact h
    refine (H1 n (by linarith)).trans ?_
    have e1 : (n : ℝ) ^ (1 - (1 : ℝ) / 400) = n * (n : ℝ) ^ (-((1 : ℝ) / 400)) := by
      rw [sub_eq_add_neg, Real.rpow_add hn', Real.rpow_one]
    have e2 : Real.log (n * Q) = t + L := Real.log_mul hn'.ne' hQ.ne'
    have e3 : (1 : ℝ) / Q = Real.exp (-L) := by
      rw [Real.exp_neg, hLdef, Real.exp_log hQ, one_div]
    have hLL : L ≤ L ^ 2 := by nlinarith
    have e4 : (t + L) ^ 2 ≤ 4 * L ^ 4 := by
      have h1 : t + L ≤ 2 * L ^ 2 := by linarith
      have h2 : (t + L) ^ 2 ≤ (2 * L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      have : (2 * L ^ 2) ^ 2 = 4 * L ^ 4 := by ring
      linarith
    have e5 : 1 ≤ L ^ 4 * (1 / t ^ 2) := by
      rw [mul_one_div, le_div_iff₀ ht2, one_mul]
      have h2 : t ^ 2 ≤ (L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) htL.le 2
      have : (L ^ 2) ^ 2 = L ^ 4 := by ring
      linarith
    have e6 : (t + L) ^ 2 ≤ 4 * L ^ 8 * (1 / t ^ 2) := by
      have h1 : 4 * L ^ 4 * 1 ≤ 4 * L ^ 4 * (L ^ 4 * (1 / t ^ 2)) :=
        mul_le_mul_of_nonneg_left e5 (by positivity)
      have : 4 * L ^ 4 * (L ^ 4 * (1 / t ^ 2)) = 4 * L ^ 8 * (1 / t ^ 2) := by ring
      linarith
    have e7 : Real.exp (-L) * (t + L) ^ 2 ≤ Real.exp (-L) * (4 * L ^ 8 * (1 / t ^ 2)) :=
      mul_le_mul_of_nonneg_left e6 (Real.exp_pos _).le
    have e8 : 0 ≤ 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L)) * (1 / t ^ 2) := by positivity
    rw [e1, e2, div_eq_mul_one_div (n : ℝ) Q, e3]
    have e9 : (n : ℝ) ^ (-((1 : ℝ) / 400)) * (t + L) ^ 2 + Real.exp (-L) * (t + L) ^ 2 ≤
        (n : ℝ) ^ (-((1 : ℝ) / 400)) * (t + L) ^ 2 +
        (4 * L ^ 8 * Real.exp (-L) + 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L))) * (1 / t ^ 2) := by
      nlinarith
    have e10 := mul_le_mul_of_nonneg_left e9 (mul_nonneg hC₁.le hn'.le)
    refine le_trans (le_of_eq ?_) (e10.trans (le_of_eq ?_)) <;> ring
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
