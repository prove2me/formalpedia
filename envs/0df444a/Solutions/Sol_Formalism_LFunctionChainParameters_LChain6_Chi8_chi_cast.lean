-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.Chi8.chi_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:06.922869+00:00
-- url     : https://prove2.me/submissions/ac2a702a-111c-4a39-b1ae-ad1331f13137

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis

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
theorem _root_.solution (m r : ℕ) : chi ((m * 8 + r : ℕ) : ZMod 8) = chi ((r : ℕ) : ZMod 8) := by
  have h8 : ((8 : ℕ) : ZMod 8) = 0 := ZMod.natCast_self 8
  rw [Nat.cast_add, Nat.cast_mul, h8, mul_zero, zero_add]
end Formalism.LFunctionChainParameters.LChain6.Chi8
