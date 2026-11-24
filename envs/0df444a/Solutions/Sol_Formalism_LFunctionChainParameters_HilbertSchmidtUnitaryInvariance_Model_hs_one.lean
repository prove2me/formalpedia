-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model.hs_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:13.912119+00:00
-- url     : https://prove2.me/submissions/73520417-8137-4ac3-897d-a8d0bedf7264

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement

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
open Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model
theorem _root_.solution : hsSq (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
  simp [hsSq, Fin.sum_univ_two, Matrix.one_apply]; norm_num
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model
