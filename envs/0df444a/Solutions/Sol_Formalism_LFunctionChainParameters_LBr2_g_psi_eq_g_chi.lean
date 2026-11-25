-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.g_psi_eq_g_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:08.91467+00:00
-- url     : https://prove2.me/submissions/fd2ea671-088d-4ad3-9b6a-a9b527945c1a

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_primitive_value_primitive


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
theorem _root_.solution : GPsiIsGchi := by
  intro e q d _ _ ell ψ hψ hell y
  unfold GPsi Gchi
  rw [if_neg hψ, hell]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have := (Finset.mem_Icc.1 hn).1
    omega
  have h := primitive_value_primitive (H := HA e) (hostN e q d) q d (recMap e q d) ψ n (NeZero.ne _) hn0
  rw [show primVal (hostData e q d) ψ n = _ from h]
  rfl
end Formalism.LFunctionChainParameters.LBr2
