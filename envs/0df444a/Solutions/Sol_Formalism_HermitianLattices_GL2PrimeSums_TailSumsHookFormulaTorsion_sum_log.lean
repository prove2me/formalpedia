-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.sum_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:36.658534+00:00
-- url     : https://prove2.me/submissions/3619a100-162b-4a07-8c91-ab2fc20cf28e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_tele
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_log_step

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
theorem _root_.solution (M : ℕ) (hM : 2 ≤ M) (N : ℕ) (hN : M ≤ N) :
    ∑ n ∈ Ioc M N, 1 / Real.log (n : ℝ) ^ 2 / n ≤ 1 / Real.log (M : ℝ) := by
  have h := tele (fun n : ℕ => 1 / Real.log (n : ℝ) ^ 2 / n) (fun n : ℕ => 1 / Real.log (n : ℝ)) M ?_ N hN
  · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (by omega) (hM.trans hN))
    have : 0 ≤ 1 / Real.log (N : ℝ) := by
      have := Real.log_nonneg hN'
      positivity
    linarith
  · intro n hn
    have hn1 : 2 ≤ n := hM.trans hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn1
    have hs := log_step n (by omega)
    have hs0 : 0 < Real.log (n : ℝ) := Real.log_pos hn'
    set s := Real.log (n : ℝ)
    set t := Real.log ((n + 1 : ℕ) : ℝ)
    have hn2 : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    have hst : s < t := by linarith
    have ht0 : 0 < t := hs0.trans hst
    have e : 1 / s - 1 / t = (t - s) / (s * t) := by field_simp
    rw [e, div_div, one_div]
    rw [one_div] at hs
    have h1 : (t ^ 2 * ((n + 1 : ℕ) : ℝ))⁻¹ = (t ^ 2)⁻¹ * (((n + 1 : ℕ) : ℝ))⁻¹ := by
      rw [mul_inv]
    rw [h1]
    calc (t ^ 2)⁻¹ * (((n + 1 : ℕ) : ℝ))⁻¹ ≤ (t ^ 2)⁻¹ * (t - s) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (t - s) / (t * t) := by rw [div_eq_mul_inv, sq]; ring
      _ ≤ (t - s) / (s * t) := by
          apply div_le_div_of_nonneg_left (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_right hst.le ht0.le
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
