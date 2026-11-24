-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.coefficient_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.009814+00:00
-- url     : https://prove2.me/submissions/3747ddbf-1ae4-4e8c-9e6b-48e202683b40

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mco_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution : CoeffSqOf := by
  unfold CoeffSqOf
  intro hD
  unfold CoeffSq
  unfold FX.DivisorBound at hD
  have hs0 : s0 = 399 / 400 := by
    unfold s0
    norm_num
  obtain ⟨C, hC⟩ := hD (1 / 400) (by norm_num)
  have hC1 : 1 ≤ C := by
    have h := hC 1 le_rfl
    simpa using h
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro Y N U hU
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U),
      (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) := le_trans (mco_norm_le Y N hn1) (hC n hn1)
    have h2 : (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) = (n : ℝ) ^ (-(199 / 200 : ℝ)) := by
      rw [← Real.rpow_add hnpos, hs0]
      norm_num
    have h3 : (n : ℝ) ^ (-(199 / 200 : ℝ)) ≤ (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      first
        | exact Real.rpow_le_rpow_of_nonpos hUpos hUn (by norm_num)
        | exact Real.rpow_le_rpow_of_exponent_nonpos hUpos hUn (by norm_num)
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_anti₀ (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_le_inv_of_le (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
    have h4 : 0 ≤ ‖mco Y N n‖ * (n : ℝ) ^ (-s0) := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hnpos.le _)
    have h5 : ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      calc ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hnpos.le _)
        _ = C * (n : ℝ) ^ (-(199 / 200 : ℝ)) := by rw [mul_assoc, h2]
        _ ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by linarith)
    first
      | exact pow_le_pow_left h4 h5 2
      | exact pow_le_pow_left₀ h4 h5 2
      | nlinarith
  have e1 : ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 = (U : ℝ) ^ (-(199 / 100 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hUpos.le]
    norm_num
  have e2 : (U : ℝ) * (U : ℝ) ^ (-(199 / 100 : ℝ)) = (U : ℝ) ^ (-(99 / 100 : ℝ)) := by
    rw [show (U : ℝ) ^ (-(99 / 100 : ℝ)) = (U : ℝ) ^ ((1 : ℝ) + -(199 / 100 : ℝ)) by norm_num,
      Real.rpow_add hUpos, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) * (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
        rw [sum_const, Nat.card_Ioc, show 2 * U - U = U by omega, nsmul_eq_mul]
    _ = C ^ 2 * ((U : ℝ) * ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2) := by ring
    _ = C ^ 2 * (U : ℝ) ^ (-(99 / 100 : ℝ)) := by rw [e1, e2]
    _ ≤ C ^ 2 * (U : ℝ) ^ (-(197 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) (by positivity)
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
