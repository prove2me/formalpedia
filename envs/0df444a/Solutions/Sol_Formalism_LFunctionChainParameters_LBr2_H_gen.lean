-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.H_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:42:48.672514+00:00
-- url     : https://prove2.me/submissions/3757df66-9ac1-46b6-8b5c-365503ffd96d

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGroup


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
theorem _root_.solution (e : ℕ) (t : FrobeniusOrbits.HGrp e) : ∃ k : ℕ, t = (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2))) ^ k := by
  obtain ⟨-, -, -, -, -, -, -, -, ι, hι⟩ := FrobeniusOrbits.hostGroup e
  refine ⟨(Multiplicative.toAdd (ι.symm t)).val, ?_⟩
  rw [← hι, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd,
    MulEquiv.apply_symm_apply]
end Formalism.LFunctionChainParameters.LBr2
