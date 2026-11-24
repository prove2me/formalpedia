-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.w_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.091503+00:00
-- url     : https://prove2.me/submissions/2c4ff8be-f393-4398-b4d5-ae83b05f8344

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_rpow_neg_k

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
namespace Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
theorem _root_.solution (M n : ℕ) (hM : 1 ≤ M) (hn : M ≤ n) (Q : ℝ) (hQ : 1 ≤ Q) :
    (n : ℝ) ^ (-((1 : ℝ) / 400)) * Real.log (n * Q) ^ 2 ≤
      2 * Real.log (M * Q) ^ 2 * (n : ℝ) ^ (-((1 : ℝ) / 400)) +
        2 * 1600 ^ 2 * (M : ℝ) ^ (-((1 : ℝ) / 800)) * (n : ℝ) ^ (-((1 : ℝ) / 800)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
  have hQ' : 0 < Q := by linarith
  have hr0 : 0 ≤ Real.log ((n : ℝ) / M) := Real.log_nonneg (by rw [le_div_iff₀ hM']; linarith)
  have hr1 : Real.log ((n : ℝ) / M) ≤ ((n : ℝ) / M) ^ ((1 : ℝ) / 1600) / (1 / 1600) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have hl0 : 0 ≤ Real.log (M * Q) := Real.log_nonneg (by nlinarith)
  have e : Real.log (n * Q) = Real.log (M * Q) + Real.log ((n : ℝ) / M) := by
    rw [Real.log_mul hn'.ne' hQ'.ne', Real.log_mul hM'.ne' hQ'.ne', Real.log_div hn'.ne' hM'.ne']
    ring
  rw [Real.div_rpow hn'.le hM'.le] at hr1
  rw [e, rpow_neg_k n hn' 4 (-((1 : ℝ) / 400)) (by norm_num), rpow_neg_k n hn' 2 (-((1 : ℝ) / 800)) (by norm_num),
    rpow_neg_k M hM' 2 (-((1 : ℝ) / 800)) (by norm_num)]
  set p := (n : ℝ) ^ ((1 : ℝ) / 1600)
  set q := (M : ℝ) ^ ((1 : ℝ) / 1600)
  set l := Real.log (M * Q)
  set r := Real.log ((n : ℝ) / M)
  have hp : 0 < p := Real.rpow_pos_of_pos hn' _
  have hq : 0 < q := Real.rpow_pos_of_pos hM' _
  have hr2 : r ≤ 1600 * (p / q) := by
    have : p / q / (1 / 1600) = 1600 * (p / q) := by ring
    linarith
  have hr3 : r ^ 2 ≤ 1600 ^ 2 * (p ^ 2 * (q ^ 2)⁻¹) := by
    have : r ^ 2 ≤ (1600 * (p / q)) ^ 2 := pow_le_pow_left₀ hr0 hr2 2
    have e2 : (1600 * (p / q)) ^ 2 = 1600 ^ 2 * (p ^ 2 * (q ^ 2)⁻¹) := by
      field_simp
    linarith
  have h4 : (l + r) ^ 2 ≤ 2 * l ^ 2 + 2 * (1600 ^ 2 * (p ^ 2 * (q ^ 2)⁻¹)) := by
    nlinarith [sq_nonneg (l - r)]
  have h5 : (p ^ 4)⁻¹ * (l + r) ^ 2 ≤ (p ^ 4)⁻¹ * (2 * l ^ 2 + 2 * (1600 ^ 2 * (p ^ 2 * (q ^ 2)⁻¹))) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
