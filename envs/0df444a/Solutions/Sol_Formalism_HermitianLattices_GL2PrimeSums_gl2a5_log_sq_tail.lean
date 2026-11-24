-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_log_sq_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:39.29629+00:00
-- url     : https://prove2.me/submissions/ba618100-90ea-4b86-b3e9-63c4a8af4117

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_tele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ n ∈ Ioc K M, Real.log n / (n : ℝ) ^ 2 ≤ (Real.log K + 2) / (K : ℝ) := by
  apply gl2a5_tele (fun n => Real.log n / (n : ℝ) ^ 2) (fun n => (Real.log n + 2) / (n : ℝ)) K _
    (fun n => by
      have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      positivity) M
  intro n hn
  have ht : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have ht0 : (0 : ℝ) < n := by linarith
  push_cast
  set t : ℝ := (n : ℝ) with htdef
  have hL : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have hl : Real.log (t + 1) - 1 / t ≤ Real.log t := by
    have h1 : Real.log ((t + 1) / t) ≤ (t + 1) / t - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) ht0.ne'] at h1
    have h2 : (t + 1) / t - 1 = 1 / t := by field_simp; ring
    linarith
  set L := Real.log (t + 1)
  set l := Real.log t
  have hlt : L * t - 1 ≤ l * t := by
    have := mul_le_mul_of_nonneg_right hl ht0.le
    have e : (L - 1 / t) * t = L * t - 1 := by field_simp
    linarith
  have e : (l + 2) / t - (L + 2) / (t + 1) - L / (t + 1) ^ 2 =
      ((l * t + 2 * t) * (t + 1) ^ 2 - (L + 2) * t ^ 2 * (t + 1) - L * t ^ 2) / (t ^ 2 * (t + 1) ^ 2) := by
    field_simp
  have hnum : 0 ≤ (l * t + 2 * t) * (t + 1) ^ 2 - (L + 2) * t ^ 2 * (t + 1) - L * t ^ 2 := by
    have h1 : (L * t - 1 + 2 * t) * (t + 1) ^ 2 ≤ (l * t + 2 * t) * (t + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : 0 ≤ L * t := by positivity
    nlinarith
  have : 0 ≤ (l + 2) / t - (L + 2) / (t + 1) - L / (t + 1) ^ 2 := by
    rw [e]; positivity
  linarith
end Formalism.HermitianLattices.GL2PrimeSums
