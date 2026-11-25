-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.qcLift_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:06:18.475039+00:00
-- url     : https://prove2.me/submissions/5cf7a211-e960-42bd-845a-654b841c555a

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
theorem _root_.solution {N l : ℕ} [Fact l.Prime] (h : l ∣ N) (u : (ZMod N)ˣ) :
    changeLevel h (qc l) (u : ZMod N)
      = ((((quadraticChar (ZMod l)).toUnitHom (ZMod.unitsMap h u) : ℤˣ) : ℤ) : ℂ) := by
  rw [changeLevel_eq_cast_of_dvd]
  unfold qc
  rw [MulChar.ringHomComp_apply]
  simp [ZMod.unitsMap_val]
end Formalism.LFunctionChainParameters.LBr2
