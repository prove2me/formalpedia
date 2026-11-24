-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.sum_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:36.92999+00:00
-- url     : https://prove2.me/submissions/24acbb25-08df-48ab-8798-0e2ca8652593

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
theorem _root_.solution (δ : ℝ) (hδ : 0 < δ) (M : ℕ) (hM : 1 ≤ M) (N : ℕ) (hN : M ≤ N) :
    ∑ n ∈ Ioc M N, (n : ℝ) ^ (-δ) / n ≤ (M : ℝ) ^ (-δ) / δ := by
  have h := tele (fun n : ℕ => (n : ℝ) ^ (-δ) / n) (fun n : ℕ => (n : ℝ) ^ (-δ) / δ) M ?_ N hN
  · have : 0 ≤ (N : ℝ) ^ (-δ) / δ := by positivity
    linarith
  · intro n hn
    have hn1 : 1 ≤ n := hM.trans hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn2 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hs := log_step n hn1
    rw [Real.rpow_def_of_pos hn', Real.rpow_def_of_pos hn2]
    set s := Real.log (n : ℝ)
    set t := Real.log ((n + 1 : ℕ) : ℝ)
    have e1 : Real.exp (s * -δ) = Real.exp (t * -δ) * Real.exp (δ * (t - s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : δ * (t - s) + 1 ≤ Real.exp (δ * (t - s)) := Real.add_one_le_exp _
    have e3 : 0 < Real.exp (t * -δ) := Real.exp_pos _
    rw [e1, ← sub_div, le_div_iff₀ hδ, div_eq_mul_one_div]
    have e4 : Real.exp (t * -δ) * (1 / ((n + 1 : ℕ) : ℝ)) ≤ Real.exp (t * -δ) * (t - s) :=
      mul_le_mul_of_nonneg_left hs e3.le
    have e5 : Real.exp (t * -δ) * (δ * (t - s) + 1) ≤ Real.exp (t * -δ) * Real.exp (δ * (t - s)) :=
      mul_le_mul_of_nonneg_left e2 e3.le
    nlinarith
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
