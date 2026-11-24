-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.Chi8.tm_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:26.497521+00:00
-- url     : https://prove2.me/submissions/4b414d1a-ce62-4795-9f3d-91ae2f4658c5

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
theorem _root_.solution (s : ℂ) (m r : ℕ) (hr : 0 < r) :
    tm s (m * 8 + r) = chi ((r : ℕ) : ZMod 8) * ((8 * (m : ℝ) + (r : ℝ) : ℝ) : ℂ) ^ (-s) := by
  unfold tm
  rw [LSeries.term_of_ne_zero (by omega), chi_cast, Complex.cpow_neg, div_eq_mul_inv]
  congr 3
  push_cast
  ring
end Formalism.LFunctionChainParameters.LChain6.Chi8
