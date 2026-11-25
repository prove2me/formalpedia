-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.qc_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:06.390387+00:00
-- url     : https://prove2.me/submissions/9d652a8f-8c20-4766-bb38-00c65c243f49

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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : qc q ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact h2)
  have h1 := DFunLike.congr_fun h (a : ZMod q)
  rw [qc, MulChar.ringHomComp_apply, ha, MulChar.one_apply_coe] at h1
  norm_num at h1
end Formalism.LFunctionChainParameters.LBr2
