-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.Chi8.block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:46:53.204662+00:00
-- url     : https://prove2.me/submissions/c2a49dca-740b-4b65-ab45-35e2ac7f1c2b

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_chi0
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_chi1
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_chi2
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_chi3
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_chi4
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_chi5
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_chi6
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_chi7
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_tm_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_tm_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain6 Formalism.LFunctionChainParameters.LChain6.Chi8
open Formalism.ZF.ComplexPowerDifferenceIntegral
namespace Formalism.LFunctionChainParameters.LChain6.Chi8
theorem _root_.solution (s : ℂ) (m : ℕ) : ∑ r : Fin 8, tm s (m * 8 + (r : ℕ)) = g s m := by
  rw [Fin.sum_univ_eight]
  change tm s (m * 8 + 0) + tm s (m * 8 + 1) + tm s (m * 8 + 2) + tm s (m * 8 + 3) + tm s (m * 8 + 4)
    + tm s (m * 8 + 5) + tm s (m * 8 + 6) + tm s (m * 8 + 7) = g s m
  rw [tm_zero s m 0 chi0, tm_zero s m 2 chi2, tm_zero s m 4 chi4, tm_zero s m 6 chi6,
    tm_eval s m 1 (by norm_num), tm_eval s m 3 (by norm_num), tm_eval s m 5 (by norm_num),
    tm_eval s m 7 (by norm_num), chi1, chi3, chi5, chi7]
  unfold g
  simp only [Nat.cast_ofNat, Nat.cast_one]
  ring
end Formalism.LFunctionChainParameters.LChain6.Chi8
