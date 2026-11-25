-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.g_psi_at_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:30.312357+00:00
-- url     : https://prove2.me/submissions/bf9d2a7a-3652-4e19-a3b7-594211fecd57

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_ell_is_log_derivative
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_g_zeta_eq_g_one
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_g_psi_eq_g_chi

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
theorem _root_.solution : GPsiHost := by
  intro e q d _ _
  refine ⟨fun ψ hψ y => g_psi_eq_g_chi e q d _ ψ hψ (ell_is_log_derivative e q d ψ) y, fun y => ?_⟩
  unfold GPsi
  rw [if_pos rfl, g_zeta_eq_g_one y]
end Formalism.LFunctionChainParameters.LBr2
