-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.comp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:40:29.350419+00:00
-- url     : https://prove2.me/submissions/89bd5136-fa3f-47d4-81f1-5909b3d276ee

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
theorem _root_.solution (ψ : AddChar (E0 × HA e) ℂ) (f : ZMod 2 → E0 × HA e) (f0 : f 0 = 0) (h1 : ψ (f 1) = -1) (s : ℤˣ) :
    ψ (f (Multiplicative.toAdd (LHost.sgn2 s))) = ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [map_one, toAdd_one, f0, AddChar.map_zero_eq_one]
    simp
  · have : Multiplicative.toAdd (LHost.sgn2 (-1)) = 1 := by decide
    rw [this, h1]
    simp
end Formalism.LFunctionChainParameters.LBr2
