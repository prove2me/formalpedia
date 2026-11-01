-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.uniform_surplus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:39.083375+00:00
-- url     : https://prove2.me/submissions/d29f7c9a-0ccf-4cc2-8ef6-191ce359ac49

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open MeasureTheory ProbabilityTheory
open CohenPriceFairness.LocalWelfare

theorem solution {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) (hpb : p ≤ b) :
    ∫ v, max (v - p) 0 ∂(uniformLaw b) = (b - p) ^ 2 / (2 * b) := by
  unfold uniformLaw
  rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hb.le,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.le]
  have h1 : ∫ v in (0:ℝ)..b, max (v - p) 0 = (∫ v in (0:ℝ)..p, max (v - p) 0)
      + ∫ v in p..b, max (v - p) 0 := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;>
      apply Continuous.intervalIntegrable <;> fun_prop
  have h2 : ∫ v in (0:ℝ)..p, max (v - p) 0 = ∫ v in (0:ℝ)..p, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hp] at hx
    simp only
    exact max_eq_right (by linarith [hx.2])
  have h3 : ∫ v in p..b, max (v - p) 0 = ∫ v in p..b, (v - p) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hpb] at hx
    simp only
    exact max_eq_left (by linarith [hx.1])
  rw [h1, h2, h3, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring
