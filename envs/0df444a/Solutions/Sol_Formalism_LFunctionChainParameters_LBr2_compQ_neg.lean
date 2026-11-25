-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.compQ_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:26.863768+00:00
-- url     : https://prove2.me/submissions/596cacf1-e599-4fb9-bb1b-86243cb3566a

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_qcLift_apply
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_comp_neg

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
theorem _root_.solution (ψ : AddChar (E0 × HA e) ℂ) (h1 : ψ ((0, 1), 0) = -1) (u : (ZMod (hostN e q d))ˣ) :
    changeLevel (q_dvd_hostN e q d) (qc q) (u : ZMod _)
      = ψ ((0, sQ q (ZMod.unitsMap (q_dvd_hostN e q d) u)), 0) := by
  rw [qcLift_apply]
  exact (comp_neg ψ (fun a => ((0, a), 0)) rfl h1 _).symm
end Formalism.LFunctionChainParameters.LBr2
