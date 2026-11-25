-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.box_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:56:31.913415+00:00
-- url     : https://prove2.me/submissions/fbad9d16-6570-4fd6-9db9-4476ffd999c7

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
theorem _root_.solution {N : ℕ} [NeZero N] {Q : ℝ} (hQ : 0 ≤ Q) {χ : DirichletCharacter ℂ N} (h : ZeroFreeBox Q χ) (σ : ℝ)
    (hσ : 1 - 1 / 400 < σ) : LFunction χ (σ : ℂ) ≠ 0 :=
  h σ (by simpa using hσ) (by simpa using hQ)
end Formalism.LFunctionChainParameters.LBr2
