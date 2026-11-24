-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.zBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:26.504797+00:00
-- url     : https://prove2.me/submissions/89771fed-dfba-4866-9d43-b912c5482e1d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_natIneq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 800000
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : Formalism.HermitianLattices.CumulantEstimateDefs.PartitionFunctionBound := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.PartitionFunctionBound
  intro C' hC'
  refine ⟨8 * C' + 1, by linarith, ?_⟩
  intro C'' hC'' p q ε₀ hp hq hexp he1
  push_cast at hexp ⊢
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hM : (1:ℝ) ≤ (p:ℝ) * q := by nlinarith
  have hε0 : 0 < ε₀ := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hCpos : 0 < C'' := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = C' * (ε₀ / (C'' * ((p:ℝ) * q))) := ⟨_, rfl⟩
  rw [← hδ]
  have hCi : C'' * C''⁻¹ = 1 := mul_inv_cancel₀ hCpos.ne'
  have hMi : ((p:ℝ) * q) * ((p:ℝ) * q)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  have hCi0 : 0 < C''⁻¹ := inv_pos.2 hCpos
  have hMi0 : 0 < ((p:ℝ) * q)⁻¹ := inv_pos.2 (by linarith)
  have hδ' : δ = C' * ε₀ * C''⁻¹ * ((p:ℝ) * q)⁻¹ := by
    rw [hδ, div_eq_mul_inv, mul_inv]
    ring
  have k1 : 8 * C' * C''⁻¹ ≤ C'' * C''⁻¹ := mul_le_mul_of_nonneg_right (by linarith) hCi0.le
  have hMδ : ((p:ℝ) * q) * δ = C' * C''⁻¹ * ε₀ := by
    rw [hδ']
    linear_combination (C' * ε₀ * C''⁻¹) * hMi
  have k2 := mul_le_mul_of_nonneg_right k1 hε0.le
  have k2' : C'' * C''⁻¹ * ε₀ = ε₀ := by rw [hCi, one_mul]
  have hMδ8 : ((p:ℝ) * q) * δ ≤ ε₀ / 8 := by linarith
  have hδ0 : 0 ≤ δ := by
    rw [hδ']
    exact mul_nonneg (mul_nonneg (mul_nonneg hC' hε0.le) hCi0.le) hMi0.le
  have hδ1 : δ ≤ ε₀ / 8 := by linarith [mul_le_mul_of_nonneg_right hM hδ0]
  refine ⟨by linarith, ?_⟩
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) (p * q)
  push_cast at hb
  rw [← sub_eq_add_neg] at hb
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (1 - δ) ^ (p * q) := ⟨_, rfl⟩
  rw [inv_pow, ← hY]
  rw [← hY] at hb
  have hYlow : 1 - ε₀ / 8 ≤ Y := by linarith
  have hY1 : Y ≤ 1 := by
    rw [hY]
    first
      | exact pow_le_one₀ (by linarith) (by linarith)
      | exact pow_le_one _ (by linarith) (by linarith)
  have hYpos : 0 < Y := by linarith
  have hU : (1 - ε₀) * (1 - ε₀)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  have hV : Y * Y⁻¹ = 1 := mul_inv_cancel₀ hYpos.ne'
  have hU0 : 0 < (1 - ε₀)⁻¹ := inv_pos.2 (by linarith)
  have hV0 : 0 < Y⁻¹ := inv_pos.2 hYpos
  have hU1 : 1 ≤ (1 - ε₀)⁻¹ := by linarith [mul_pos hε0 hU0]
  have hV1 : 1 ≤ Y⁻¹ := by linarith [mul_nonneg (sub_nonneg.2 hY1) hV0.le]
  have hUV : (1 - ε₀)⁻¹ - Y⁻¹ = (1 - ε₀)⁻¹ * Y⁻¹ * (Y - (1 - ε₀)) := by
    linear_combination (-(1 - ε₀)⁻¹) * hV + Y⁻¹ * hU
  have hY7 : 7 * ε₀ / 8 ≤ Y - (1 - ε₀) := by linarith
  have hUV0 : 0 ≤ (1 - ε₀)⁻¹ * Y⁻¹ := (mul_pos hU0 hV0).le
  have key := mul_le_mul_of_nonneg_left hY7 hUV0
  have hUV1 : 1 * 1 ≤ (1 - ε₀)⁻¹ * Y⁻¹ := mul_le_mul hU1 hV1 zero_le_one hU0.le
  have hE0 : Real.exp (-(2 * (p:ℝ) * q)) ≤ ε₀ := by
    refine le_trans (Real.exp_le_exp.2 ?_) hexp
    linarith [mul_nonneg (sub_nonneg.2 hpR) (sub_nonneg.2 hqR)]
  by_cases h11 : p = 1 ∧ q = 1
  · obtain ⟨hp1, hq1⟩ := h11
    have hp1' : (p:ℝ) = 1 := by exact_mod_cast hp1
    have hq1' : (q:ℝ) = 1 := by exact_mod_cast hq1
    rw [hp1', hq1'] at hexp
    have he2 : Real.exp 2 ≤ 8 := by
      have h := Real.exp_one_lt_d9
      have h' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [h']
      have h3 : Real.exp 1 ≤ 2.72 := by linarith
      calc Real.exp 1 * Real.exp 1 ≤ 2.72 * 2.72 := mul_le_mul h3 h3 (Real.exp_pos 1).le (by norm_num)
        _ ≤ 8 := by norm_num
    have hm2 : Real.exp (-2) * Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hε8 : 1 / 8 ≤ ε₀ := by
      have : Real.exp (-(1 + 1)) = Real.exp (-2) := by norm_num
      rw [this] at hexp
      have h5 := mul_le_mul_of_nonneg_left he2 (Real.exp_pos (-2)).le
      linarith
    have hU8 : 8 / 7 ≤ (1 - ε₀)⁻¹ := by
      linarith [mul_le_mul_of_nonneg_right hε8 hU0.le]
    have hUVb : (1 - ε₀)⁻¹ * 1 ≤ (1 - ε₀)⁻¹ * Y⁻¹ := mul_le_mul_of_nonneg_left hV1 hU0.le
    have k3 := mul_le_mul_of_nonneg_right (show 8 / 7 ≤ (1 - ε₀)⁻¹ * Y⁻¹ by linarith)
      (show (0:ℝ) ≤ 7 * ε₀ / 8 by linarith)
    linarith
  · have hnat := natIneq p q hp hq h11
    have hreal : (p:ℝ) + q + 1 ≤ 2 * p * q := by exact_mod_cast hnat
    have hE1 : Real.exp (-(2 * (p:ℝ) * q)) ≤ Real.exp (-((p:ℝ) + q) + -1) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_add] at hE1
    have hx : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hm1 : Real.exp (-1) ≤ 1 / 2 := by linarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-1)).le]
    have hE2 : Real.exp (-((p:ℝ) + q)) * Real.exp (-1) ≤ ε₀ * (1 / 2) :=
      mul_le_mul hexp hm1 (Real.exp_pos _).le hε0.le
    have k4 := mul_le_mul_of_nonneg_right hUV1 (show (0:ℝ) ≤ 7 * ε₀ / 8 by linarith)
    linarith
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
