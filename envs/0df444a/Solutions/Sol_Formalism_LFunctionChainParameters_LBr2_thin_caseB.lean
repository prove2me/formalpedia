-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.thin_caseB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:01:12.485946+00:00
-- url     : https://prove2.me/submissions/d0718042-bc88-4cec-b072-faeee9b50fa7

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
theorem _root_.solution (a A μ s R Lb : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (hμ2 : 2 ≤ μ) (hs0 : 0 ≤ s) (hsμ : s < μ)
    (hμL : μ ≤ Lb) (hv : Lb * R / 2 ≤ s ^ 2) (hL6 : Lb ^ 6 = R ^ 10) (hR0 : 0 ≤ R) :
    A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ 8 * A * (((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10) * Real.exp (-(a / 8 * R)) := by
  have hM0 : 0 < μ + s := by linarith
  have hexpo : -a * s ^ 2 / (μ + s) ≤ -(a / 8 * R) + -(a / 8 * R) := by
    have h8 : R / 4 ≤ s ^ 2 / (μ + s) := by
      rw [div_le_div_iff₀ (by norm_num) hM0]
      have h10 : μ + s ≤ 2 * Lb := by linarith
      have h12 : R * (μ + s) ≤ R * (2 * Lb) := mul_le_mul_of_nonneg_left h10 hR0
      linarith
    have e : -a * s ^ 2 / (μ + s) = -(a * (s ^ 2 / (μ + s))) := by ring
    have m1 := mul_le_mul_of_nonneg_left h8 ha.le
    rw [e]
    linarith
  have hcube : (μ + s + s ^ 2) ^ 3 ≤ 8 * R ^ 10 := by
    have h9 : μ + s + s ^ 2 ≤ 2 * Lb ^ 2 := by
      have k1 : s ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hs0 hsμ.le 2
      have k2 : μ ^ 2 ≤ Lb ^ 2 := pow_le_pow_left₀ (by linarith) hμL 2
      have k3 : 2 * μ ≤ μ ^ 2 := by nlinarith
      linarith
    calc (μ + s + s ^ 2) ^ 3 ≤ (2 * Lb ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h9 3
      _ = 8 * Lb ^ 6 := by ring
      _ = 8 * R ^ 10 := by rw [hL6]
  have hK := pow_mul_exp_neg_le 10 (a / 8) R (by positivity) hR0
  have hE := Real.exp_le_exp.2 hexpo
  calc A * (μ + s + s ^ 2) ^ 3 * Real.exp (-a * s ^ 2 / (μ + s))
      ≤ A * (8 * R ^ 10) * Real.exp (-(a / 8 * R) + -(a / 8 * R)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcube hA) hE (Real.exp_pos _).le (by positivity)
    _ = 8 * A * (R ^ 10 * Real.exp (-(a / 8 * R))) * Real.exp (-(a / 8 * R)) := by
        rw [Real.exp_add]; ring
    _ ≤ 8 * A * (((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10) * Real.exp (-(a / 8 * R)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) (Real.exp_pos _).le
end Formalism.LFunctionChainParameters.LBr2
