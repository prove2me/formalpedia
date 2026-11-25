-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.component_two_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:38:21.194971+00:00
-- url     : https://prove2.me/submissions/1a2fcf01-9996-4562-83ab-9fa2e4c8b80e

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_H_gen
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_psi_H_pow
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_chi_eight_lift_class

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
theorem _root_.solution (ψ : AddChar (E0 × HA e) ℂ) (h8 : 8 ∣ 2 ^ (e + 2))
    (h1 : ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (TwoAdicCyclotomicDecomposition.u5 (e + 2)))) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (h8.trans (two_dvd_hostN e q d)) chi8 (u : ZMod _)
      = ψ ((0, 0), Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) := by
  obtain ⟨k, hk⟩ := H_gen e (FrobeniusOrbits.hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))
  rw [hk, psi_H_pow, h1, changeLevel_trans chi8 h8 (two_dvd_hostN e q d), changeLevel_eq_cast_of_dvd,
    ← chi_eight_lift_class e h8 _ k hk, ZMod.unitsMap_val]
end Formalism.LFunctionChainParameters.LBr2
