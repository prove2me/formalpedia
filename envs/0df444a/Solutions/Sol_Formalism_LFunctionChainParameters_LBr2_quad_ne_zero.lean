-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.quad_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:38:19.717204+00:00
-- url     : https://prove2.me/submissions/ff475b92-faa5-4a27-b07a-bdc3bf9c7e0e

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_psC_apply
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_chC_apply
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_chpsC_apply
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_one_ne_zero2

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
theorem _root_.solution (e : ℕ) : (psC : AddChar (E0 × HA e) ℂ) ≠ 0 ∧ (chC : AddChar (E0 × HA e) ℂ) ≠ 0 ∧
    (chpsC : AddChar (E0 × HA e) ℂ) ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := DFunLike.congr_fun h (((0, 1), 0) : E0 × HA e)
    rw [psC_apply, AddChar.zero_apply] at this
    norm_num [one_ne_zero2] at this
  · have := DFunLike.congr_fun h (((1, 0), 0) : E0 × HA e)
    rw [chC_apply, AddChar.zero_apply] at this
    norm_num [one_ne_zero2] at this
  · have := DFunLike.congr_fun h (((1, 0), 0) : E0 × HA e)
    rw [chpsC_apply, AddChar.zero_apply] at this
    norm_num [one_ne_zero2] at this
end Formalism.LFunctionChainParameters.LBr2
