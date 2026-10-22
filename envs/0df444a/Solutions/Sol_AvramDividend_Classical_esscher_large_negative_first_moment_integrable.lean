-- Prove2me | solution 1 for AvramDividend.Classical.esscher_large_negative_first_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T00:02:21.610871+00:00
-- url     : https://prove2.me/submissions/0ed7536a-6b3f-4baf-9f9c-7f0bb53e47d9

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_large_uniform
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter

theorem solution (ν : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hfinite : ν (Iic (-1 : ℝ)) < ⊤) :
    IntegrableOn (fun y : ℝ => (-y) * Real.exp (φ * y))
      (Iic (-1 : ℝ)) ν := by
  have hm : AEStronglyMeasurable
      (fun y : ℝ => (-y) * Real.exp (φ * y))
      (ν.restrict (Iic (-1 : ℝ))) := by
    have hc : Continuous
        (fun y : ℝ => (-y) * Real.exp (φ * y)) := by fun_prop
    exact hc.measurable.aestronglyMeasurable
  apply IntegrableOn.of_bound hfinite hm (1 / φ)
  filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
  have hy0 : 0 ≤ -y := by
    have hle : y ≤ -1 := hy
    linarith
  have hb := gaussian_esscher_drift_large_uniform φ (-y) hφ hy0
  have heq : (-φ) * (-y) = φ * y := by ring
  rw [heq] at hb
  have hnn : 0 ≤ (-y) * Real.exp (φ * y) :=
    mul_nonneg hy0 (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hb
