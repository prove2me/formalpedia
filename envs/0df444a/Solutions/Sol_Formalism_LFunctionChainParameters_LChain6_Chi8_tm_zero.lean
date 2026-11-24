-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.Chi8.tm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:27.273529+00:00
-- url     : https://prove2.me/submissions/2a96789f-fbc7-48b4-869d-4244fddda8b3

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_chi_cast

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
theorem _root_.solution (s : ℂ) (m r : ℕ) (h : chi ((r : ℕ) : ZMod 8) = 0) : tm s (m * 8 + r) = 0 := by
  unfold tm
  rw [LSeries.term_def]
  split_ifs
  · rfl
  · rw [chi_cast, h, zero_div]
end Formalism.LFunctionChainParameters.LChain6.Chi8
