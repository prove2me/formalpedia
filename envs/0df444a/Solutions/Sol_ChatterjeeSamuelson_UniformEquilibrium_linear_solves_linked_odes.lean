-- Prove2me | solution 1 for ChatterjeeSamuelson.UniformEquilibrium.linear_solves_linked_odes
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:56:52.433987+00:00
-- url     : https://prove2.me/submissions/12d832a3-0ebc-414e-a49b-79d221e0a5b0

import Definitions.Def_ChatterjeeSamuelson_Shared_unif
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerLinear
import Mathlib.Probability.CDF
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Set
open ChatterjeeSamuelson

private theorem cdf_unif (vbar y : ℝ) (hv : 0 < vbar) (hy : y ∈ Icc (0:ℝ) vbar) :
    cdf (Shared.unif vbar) y = y/vbar := by
  have hvol : volume (Icc (0:ℝ) vbar) = ENNReal.ofReal vbar := by simp [Real.volume_Icc]
  haveI : IsProbabilityMeasure (Shared.unif vbar) :=
    cond_isProbabilityMeasure_of_finite (by simpa [hvol] using (ne_of_gt (ENNReal.ofReal_pos.mpr hv)))
      (by simp [hvol])
  rw [cdf_eq_real]
  change (volume[|Icc (0:ℝ) vbar] (Iic y)).toReal = _
  rw [cond_apply measurableSet_Icc]
  have hi : Icc (0:ℝ) vbar ∩ Iic y = Icc 0 y := by ext z; simp; grind
  rw [hi,hvol,Real.volume_Icc]
  simp [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal hv.le,
    ENNReal.toReal_ofReal hy.1,div_eq_mul_inv,mul_comm]

theorem solution (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hvbar : 0 < vbar) :
    (∀ y ∈ Icc (0 : ℝ) vbar, ∀ x : ℝ, Shared.buyerLinear k vbar x = Shared.sellerLinear k vbar y →
        k * cdf (Shared.unif vbar) y * deriv (Shared.sellerLinear k vbar) y
            + (1 / vbar) * Shared.sellerLinear k vbar y = x * (1 / vbar)) ∧
      (∀ x ∈ Icc (0 : ℝ) vbar, ∀ y : ℝ, Shared.sellerLinear k vbar y = Shared.buyerLinear k vbar x →
        (1 - k) * (1 - cdf (Shared.unif vbar) x) * deriv (Shared.buyerLinear k vbar) x
            - (1 / vbar) * Shared.buyerLinear k vbar x = -(y * (1 / vbar))) := by
  have hd : 2-k ≠ 0 := by linarith
  have he : 1+k ≠ 0 := by linarith
  have hv := hvbar.ne'
  have hS : ∀ y, deriv (Shared.sellerLinear k vbar) y = 1/(2-k) := by
    intro y
    exact (show HasDerivAt (Shared.sellerLinear k vbar) (1/(2-k)) y from
      ((hasDerivAt_id y).div_const (2-k)).add_const _).deriv
  have hB : ∀ x, deriv (Shared.buyerLinear k vbar) x = 1/(1+k) := by
    intro x
    exact (show HasDerivAt (Shared.buyerLinear k vbar) (1/(1+k)) x from
      ((hasDerivAt_id x).div_const (1+k)).add_const _).deriv
  constructor
  · intro y hy x hxy
    rw [cdf_unif vbar y hvbar hy,hS]
    simp only [Shared.buyerLinear,Shared.sellerLinear] at hxy ⊢
    field_simp at hxy ⊢
    nlinarith
  · intro x hx y hyx
    rw [cdf_unif vbar x hvbar hx,hB]
    simp only [Shared.buyerLinear,Shared.sellerLinear] at hyx ⊢
    field_simp at hyx ⊢
    nlinarith
