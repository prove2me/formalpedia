-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_mertens_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:28.386184+00:00
-- url     : https://prove2.me/submissions/a286bd2f-17ca-4968-ad53-14d525abde43

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailMertens
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_mertens_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (N : ℕ) :
    ∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ) / (n : ℝ) ≤
      (∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ)) / ((N : ℝ) + 1)
        + (Real.log 4 + 4) * Real.log ((N : ℝ) + 1) := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  induction N with
  | zero => simp
  | succ M ih =>
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
    have hM2 : (0:ℝ) < (M:ℝ) + 1 + 1 := by positivity
    have hB := tail_mertens_psi (M + 1)
    push_cast at hB
    have hlog : 1 / ((M:ℝ) + 1 + 1) ≤ Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1) := by
      rw [← Real.log_div hM2.ne' hM1.ne']
      have h := Real.one_sub_inv_le_log_of_pos (x := ((M:ℝ) + 1 + 1) / ((M:ℝ) + 1)) (by positivity)
      calc 1 / ((M:ℝ) + 1 + 1) = 1 - (((M:ℝ) + 1 + 1) / ((M:ℝ) + 1))⁻¹ := by
            field_simp
            ring
        _ ≤ _ := h
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 + 1 by omega)]
    push_cast
    set B := ∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ) with hBdef
    set L := (Λ (M + 1 + 1) : ℝ) with hLdef
    have key1 : B / ((M:ℝ) + 1) ≤ (B + (Real.log 4 + 4)) / ((M:ℝ) + 1 + 1) := by
      rw [div_le_div_iff₀ hM1 hM2]
      nlinarith
    have key2 : (Real.log 4 + 4) / ((M:ℝ) + 1 + 1) ≤
        (Real.log 4 + 4) * (Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hlog hc
    rw [add_div] at key1 ⊢
    linarith
end Formalism.HermitianLattices.Ext.BoxTail
