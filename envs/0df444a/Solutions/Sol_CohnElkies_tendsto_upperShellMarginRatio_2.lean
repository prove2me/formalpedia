-- Prove2me | solution 2 for CohnElkies.tendsto_upperShellMarginRatio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:27.849608+00:00
-- url     : https://prove2.me/submissions/4344309a-f691-40d7-9961-2ec22928c7d6

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution :
    Tendsto upperShellMarginRatio
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hu : Tendsto (fun ε : ℝ => (ε⁻¹) ^ 2 / 8) (𝓝[>] (0:ℝ)) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero).atTop_div_const (by norm_num)
  have hg : Tendsto (fun ε : ℝ => (5000 * 704 * Real.exp 5) *
      (((ε⁻¹) ^ 2 / 8) ^ 2 * Real.exp (-((ε⁻¹) ^ 2 / 8)))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hu).const_mul
      (5000 * 704 * Real.exp 5)
    rw [mul_zero] at this
    exact this
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 ≤ upperShellMarginRatio ε ∧
      upperShellMarginRatio ε ≤ (5000 * 704 * Real.exp 5) *
        (((ε⁻¹) ^ 2 / 8) ^ 2 * Real.exp (-((ε⁻¹) ^ 2 / 8))) := by
    intro ε h0 h1
    have ht : 1 < ε⁻¹ := one_lt_inv₀ h0 |>.2 h1
    have htp : 0 < ε⁻¹ := inv_pos.2 h0
    have hlog0 : 0 ≤ Real.log (1 / ε) := by
      rw [one_div]; exact Real.log_nonneg ht.le
    have hlogt : Real.log (1 / ε) ≤ ε⁻¹ := by
      rw [one_div]; have := Real.log_le_sub_one_of_pos htp; linarith
    have hden : shellWeight ε * Real.exp ((ε / 2) * shellLocation ε) =
        Real.exp ((ε⁻¹) ^ 2 / 8) := by
      unfold shellWeight shellLocation
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have hA0 : 0 ≤ shortEndpoint ε + (shortCutoff ε)⁻¹ := by
      unfold shortEndpoint shortCutoff; positivity
    have hA : shortEndpoint ε + (shortCutoff ε)⁻¹ ≤ 704 * ((ε⁻¹) ^ 2 / 8) ^ 2 := by
      unfold shortEndpoint shortCutoff
      rw [← inv_pow]
      have h3 : ε⁻¹ ^ 3 ≤ ε⁻¹ ^ 4 := pow_le_pow_right₀ ht.le (by norm_num)
      have h4 : ε⁻¹ ≤ ε⁻¹ ^ 4 := by
        calc ε⁻¹ = ε⁻¹ ^ 1 := (pow_one _).symm
          _ ≤ ε⁻¹ ^ 4 := pow_le_pow_right₀ ht.le (by norm_num)
      nlinarith
    have hB : Real.exp ((ε / 2) * shortEndpoint ε) ≤ Real.exp 5 := by
      apply Real.exp_le_exp.2
      unfold shortEndpoint
      have : ε * ε⁻¹ = 1 := mul_inv_cancel₀ h0.ne'
      nlinarith
    unfold upperShellMarginRatio
    rw [hden]
    have hE := Real.exp_pos ((ε⁻¹) ^ 2 / 8)
    constructor
    · positivity
    · rw [div_le_iff₀ hE, Real.exp_neg]
      have hEE : (Real.exp ((ε⁻¹) ^ 2 / 8))⁻¹ * Real.exp ((ε⁻¹) ^ 2 / 8) = 1 := by
        rw [inv_mul_cancel₀ hE.ne']
      have hB0 := Real.exp_pos ((ε / 2) * shortEndpoint ε)
      calc 5000 * (shortEndpoint ε + (shortCutoff ε)⁻¹) * Real.exp ((ε / 2) * shortEndpoint ε)
          ≤ 5000 * (704 * ((ε⁻¹) ^ 2 / 8) ^ 2) * Real.exp 5 := by
            apply mul_le_mul (by linarith) hB hB0.le (by positivity)
        _ = 5000 * 704 * Real.exp 5 * (((ε⁻¹) ^ 2 / 8) ^ 2 *
              ((Real.exp ((ε⁻¹) ^ 2 / 8))⁻¹ * Real.exp ((ε⁻¹) ^ 2 / 8))) := by
            rw [hEE]; ring
        _ = _ := by ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact (key ε hε.1 hε.2).1
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact (key ε hε.1 hε.2).2

