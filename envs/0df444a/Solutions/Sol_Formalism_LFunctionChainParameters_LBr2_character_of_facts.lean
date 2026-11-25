-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.character_of_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:33.441813+00:00
-- url     : https://prove2.me/submissions/371ae72c-3efa-47d4-a422-985e518ad83b

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_dirChar_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_dirichlet_character_injective


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
theorem _root_.solution : ChiOfFacts := by
  intro e q d _ _ h ψ
  refine ⟨primitiveCharacter_isPrimitive _, ⟨conductor_dvd_level _, changeLevel_primitiveCharacter _⟩, fun hψ => ?_⟩
  have hne : dirChar (recMap e q d) ψ ≠ 1 := by
    intro h1
    rw [← dirChar_zero e q d] at h1
    exact hψ (dirichlet_character_injective e q d h h1)
  have hc : condOf e q d ψ ≠ 1 := fun h1 => hne (eq_one_iff_conductor_eq_one.2 h1)
  refine ⟨fun h1 => hne ?_, hc⟩
  have h2 := changeLevel_primitiveCharacter (dirChar (recMap e q d) ψ)
  rw [show (dirChar (recMap e q d) ψ).primitiveCharacter = 1 from h1, changeLevel_one] at h2
  exact h2.symm
end Formalism.LFunctionChainParameters.LBr2
