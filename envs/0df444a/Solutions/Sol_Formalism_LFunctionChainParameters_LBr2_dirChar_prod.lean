-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.dirChar_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:08.987995+00:00
-- url     : https://prove2.me/submissions/6f4c4ccf-cf6a-4b1f-967f-f5ba9c70a4f2

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_psi_split
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_dirChar_unit
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_recMap_apply


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
theorem _root_.solution (ψ : AddChar (E0 × HA e) ℂ) (D2 Dq Dd : DirichletCharacter ℂ (hostN e q d))
    (h2 : ∀ u : (ZMod (hostN e q d))ˣ, D2 (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))))
    (hq : ∀ u : (ZMod (hostN e q d))ˣ, Dq (u : ZMod _) = ψ ((0, sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)), 0))
    (hd : ∀ u : (ZMod (hostN e q d))ˣ, Dd (u : ZMod _) = ψ ((sQ d (ZMod.unitsMap (d_dvd_hostN e q d) u), 0), 0)) :
    dirChar (recMap e q d) ψ = D2 * Dq * Dd := by
  apply MulChar.ext
  intro u
  rw [dirChar_unit, recMap_apply, psi_split, MulChar.mul_apply, MulChar.mul_apply, h2, hq, hd]
end Formalism.LFunctionChainParameters.LBr2
