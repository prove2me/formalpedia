-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_cN_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:26.234154+00:00
-- url     : https://prove2.me/submissions/8a7a900a-2a62-44ec-ac38-cae0f533ce87

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_KC_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_vM_major
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_inv_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_one_le_of_exp_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_one_le_log_of_exp_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_one_le_floor_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_log_le_of_le_floor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
open ArithmeticFunction (vonMangoldt)
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, cN x n ≤ C * x * Real.log x := by
  refine ⟨dA_KC * 401, Real.exp 1, fun x hx => ?_⟩
  have hx1 := dA_one_le_of_exp_le hx
  have hlog := dA_one_le_log_of_exp_le hx
  have hx0 : 0 ≤ x := by linarith
  have hN1 := dA_one_le_floor_pow hx1
  have hlogN := dA_log_le_of_le_floor hx1 hN1 le_rfl
  have h1 := dA_vM_major (fun n => min 1 (x / n)) (fun n => le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg n)))
    (fun n hn => by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      apply min_le_min_left
      push_cast
      gcongr
      linarith) ⌊x ^ 400⌋₊
  have h2 : ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, min 1 (x / (n : ℝ)) ≤ x * (1 + Real.log ⌊x ^ 400⌋₊) := by
    calc ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, min 1 (x / (n : ℝ)) ≤ ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, x * (1 / (n : ℝ)) :=
          sum_le_sum (fun n _ => by rw [mul_one_div]; exact min_le_right _ _)
      _ = x * ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, 1 / (n : ℝ) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (dA_sum_inv_le _ hN1) hx0
  have h3 : x * (1 + Real.log ⌊x ^ 400⌋₊) ≤ x * (401 * Real.log x) :=
    mul_le_mul_of_nonneg_left (by linarith) hx0
  calc ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, cN x n ≤ dA_KC * ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, min 1 (x / (n : ℝ)) := h1
    _ ≤ dA_KC * (x * (401 * Real.log x)) := mul_le_mul_of_nonneg_left (h2.trans h3) dA_KC_pos.le
    _ = _ := by ring
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
