-- Prove2me | solution 1 for DataDrivenRO.Marginal.var_pos_homog
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:50:41.73409+00:00
-- url     : https://prove2.me/submissions/7c725c44-b1bf-441e-9f5d-85cbf7197c39

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

open MeasureTheory DataDrivenRO.Marginal Pointwise in
theorem var_pos_homog_aux {d : ℕ} (P : Measure (Fin d → ℝ)) (δ : ℝ)
    (c : ℝ) (hc : 0 < c) (w : Fin d → ℝ) :
    VaR P δ (c • w) = c * VaR P δ w := by
  unfold VaR MultistageStochastic.valueAtRisk
  have hset : {y : ℝ | ENNReal.ofReal (1 - δ) ≤ P {ω | ω ⬝ᵥ (c • w) ≤ y}}
      = c • {y : ℝ | ENNReal.ofReal (1 - δ) ≤ P {ω | ω ⬝ᵥ w ≤ y}} := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    simp only [Set.mem_setOf_eq, smul_eq_mul]
    have : {ω : Fin d → ℝ | ω ⬝ᵥ (c • w) ≤ y} = {ω | ω ⬝ᵥ w ≤ c⁻¹ * y} := by
      ext ω
      simp only [Set.mem_setOf_eq, dotProduct_smul, smul_eq_mul]
      rw [le_inv_mul_iff₀ hc]
    rw [this]
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]

open MeasureTheory DataDrivenRO.Marginal in
theorem solution {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P] (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (c : ℝ) (hc : 0 < c) (w : Fin d → ℝ) :
    VaR P δ (c • w) = c * VaR P δ w := by
  exact var_pos_homog_aux P δ c hc w
