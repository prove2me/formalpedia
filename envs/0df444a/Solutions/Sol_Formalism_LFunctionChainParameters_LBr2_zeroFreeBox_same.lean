-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.zeroFreeBox_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:47:54.716346+00:00
-- url     : https://prove2.me/submissions/d87d97da-42cf-42b2-80d8-06008f67bf7e

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_same_character_g

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
theorem _root_.solution {N M : ℕ} [NeZero N] [NeZero M] {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ M}
    (hs : SameChar χ χ') {Q : ℝ} (h : ZeroFreeBox Q χ') : ZeroFreeBox Q χ := by
  intro s h1 h2
  rw [(same_character_g _ _ _ _ hs).2.2.2.1]
  exact h s h1 h2
end Formalism.LFunctionChainParameters.LBr2
