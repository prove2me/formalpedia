-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.tw_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:48:53.035155+00:00
-- url     : https://prove2.me/submissions/74c3f0cf-0000-49f4-b909-364b3f2acc1d

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
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
namespace Formalism.LFunctionChainParameters.LBr2
theorem _root_.solution {N t l : ℕ} [Fact l.Prime] (θ : DirichletCharacter ℂ t) (h : t * l ∣ N) :
    changeLevel h (tw θ l) = changeLevel ((Dvd.intro l rfl).trans h) θ
      * changeLevel ((Dvd.intro_left t rfl).trans h) (qc l) := by
  unfold tw
  rw [map_mul, ← changeLevel_trans, ← changeLevel_trans]
end Formalism.LFunctionChainParameters.LBr2
