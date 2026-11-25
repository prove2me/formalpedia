-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.thin_caseA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:10:16.966591+00:00
-- url     : https://prove2.me/submissions/43343e19-1b59-4563-b44c-23bb0cce9533

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_pow_mul_exp_neg_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction DirichletCharacter
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBr2
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBr2
theorem _root_.solution (a A μ s R : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (hμ2 : 2 ≤ μ) (hμs : μ ≤ s) (hsR : R / 2 ≤ s) :
    A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ 8 * A * (((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6) * Real.exp (-(a / 8 * R)) := by
  have hs2 : 2 ≤ s := by linarith
  have hM0 : 0 < μ + s := by linarith
  have hexpo : -a * s ^ 2 / (μ + s) ≤ -(a / 4 * s) + -(a / 8 * R) := by
    have h8 : s / 2 ≤ s ^ 2 / (μ + s) := by
      rw [div_le_div_iff₀ (by norm_num) hM0]
      nlinarith
    have e : -a * s ^ 2 / (μ + s) = -(a * (s ^ 2 / (μ + s))) := by ring
    have m1 := mul_le_mul_of_nonneg_left h8 ha.le
    have m2 := mul_le_mul_of_nonneg_left hsR ha.le
    rw [e]
    linarith
  have hcube : (μ + s + s ^ 2) ^ 3 ≤ 8 * s ^ 6 := by
    have h9 : μ + s + s ^ 2 ≤ 2 * s ^ 2 := by nlinarith
    calc (μ + s + s ^ 2) ^ 3 ≤ (2 * s ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h9 3
      _ = 8 * s ^ 6 := by ring
  have hK := pow_mul_exp_neg_le 6 (a / 4) s (by positivity) (by linarith)
  have hE := Real.exp_le_exp.2 hexpo
  calc A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ A * (8 * s ^ 6) * Real.exp (-(a / 4 * s) + -(a / 8 * R)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcube hA) hE (Real.exp_pos _).le (by positivity)
    _ = 8 * A * (s ^ 6 * Real.exp (-(a / 4 * s))) * Real.exp (-(a / 8 * R)) := by
        rw [Real.exp_add]; ring
    _ ≤ 8 * A * (((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6) * Real.exp (-(a / 8 * R)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le
end Formalism.LFunctionChainParameters.LBr2
