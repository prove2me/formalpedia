-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.text_sizes_windows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:08:06.003796+00:00
-- url     : https://prove2.me/submissions/6cb87181-0d81-4d3c-b83f-0e4acd1747b9

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution : TextSizesWindows := by
  intro ε e hε
  have hε3 : 0 < ε / 3 := by positivity
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, (|e| + 1) * Real.log x ≤ x ^ (ε / 3) := by
    have hc : 0 < (|e| + 1)⁻¹ := by positivity
    have hb := (isLittleO_log_rpow_atTop hε3).bound hc
    filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
      Real.norm_of_nonneg (Real.log_nonneg hx1)] at hx
    have : (|e| + 1) * Real.log x ≤ (|e| + 1) * ((|e| + 1)⁻¹ * x ^ (ε / 3)) := by gcongr
    rwa [mul_inv_cancel_left₀ (by positivity)] at this
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (2 * ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x0, hx0⟩ :=
    Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨x0, ?_⟩
  intro x k n lrd hx hk hkx hn hnx hlrd
  obtain ⟨⟨hl, h2x⟩, hx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨z, hz⟩ : ∃ z, z = x ^ (ε / 3) := ⟨_, rfl⟩
  rw [← hz] at hl hlrd
  have hz0 : 0 ≤ z := by rw [hz]; exact Real.rpow_nonneg hxpos.le _
  have hzz : 2 * z ≤ x ^ ε := by
    have : x ^ ε = x ^ (2 * ε / 3) * z := by
      rw [hz, ← Real.rpow_add hxpos]; congr 1; ring
    rw [this]; gcongr
  have habs : 0 ≤ |e| := abs_nonneg e
  have hxe : x ^ e ≤ Real.exp z := by
    rw [Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.2
    have : Real.log x * e ≤ Real.log x * |e| := by gcongr; exact le_abs_self e
    nlinarith
  have hlogx : Real.log x ≤ z := by nlinarith
  obtain ⟨X, hX⟩ : ∃ X, X = Real.exp z := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = Real.exp (x ^ ε) := ⟨_, rfl⟩
  have hXX : X * X ≤ B := by
    rw [hX, hB, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hX1 : 1 ≤ X := by rw [hX]; exact Real.one_le_exp hz0
  have hX0 : 0 < X := by linarith
  have hB1 : 1 ≤ B := by rw [hB]; exact Real.one_le_exp (Real.rpow_nonneg hxpos.le _)
  have hB0 : 0 < B := by linarith
  have hkX : k ≤ X := by rw [hX]; exact hkx.trans hxe
  have hnX : n ≤ X := by rw [hX]; exact hnx.trans hxe
  have hXB : X ≤ B := (le_mul_of_one_le_left hX0.le hX1).trans hXX
  have hBA : B ≤ x * B := le_mul_of_one_le_left hB0.le hx1
  have hA0 : 0 < x * B := by positivity
  unfold XppTx wppTx bpTx aTx bTx XpTx
  rw [← hz, ← hX, ← hB]
  refine ⟨hx1, hB1, by rw [hB, Real.log_exp], ?_, hkX.trans (hXB.trans hBA), by positivity, ?_, ?_, ?_⟩
  · rw [Real.log_mul hxpos.ne' hB0.ne', hB, Real.log_exp]
    linarith
  · rw [← mul_div_assoc, div_le_iff₀ hX0, mul_comm]
    gcongr
  · positivity
  · have : x * B / (x * B / X / (x * n)) = x * (n * X) := by
      field_simp
    rw [this]
    gcongr
    exact (mul_le_mul_of_nonneg_right hnX hX0.le).trans hXX
end Formalism.LFunctionChainParameters.LErr
