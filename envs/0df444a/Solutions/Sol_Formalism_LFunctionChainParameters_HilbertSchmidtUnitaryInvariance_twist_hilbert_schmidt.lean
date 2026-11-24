-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.twist_hilbert_schmidt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:55:24.165663+00:00
-- url     : https://prove2.me/submissions/7bc60e8e-9fd1-4e22-94d1-453eec69aba8

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_hs_Kp_tw
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_hs_Kd_tw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
theorem _root_.solution : TwHS := by
  intro ι _ D D' d B ga c V U hc hV hU
  exact ⟨hs_Kp_tw B ga c V U hc hV.1 hU, hs_Kd_tw B ga c V U hc hV.1 hU⟩
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
