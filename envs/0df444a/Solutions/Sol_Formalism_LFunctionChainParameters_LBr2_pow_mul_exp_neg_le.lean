-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.pow_mul_exp_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:50:25.033117+00:00
-- url     : https://prove2.me/submissions/96cc955d-4c13-482a-9432-5c1eb3e4d66e

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions

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
theorem _root_.solution (n : ℕ) (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-(b * t)) ≤ (n.factorial : ℝ) / b ^ n := by
  have h := Real.pow_div_factorial_le_exp (b * t) (by positivity) n
  have h2 : (b * t) ^ n ≤ (n.factorial : ℝ) * Real.exp (b * t) := by
    rwa [div_le_iff₀' (by positivity)] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  calc t ^ n * b ^ n = (b * t) ^ n := by rw [mul_pow]; ring
    _ ≤ _ := h2
end Formalism.LFunctionChainParameters.LBr2
