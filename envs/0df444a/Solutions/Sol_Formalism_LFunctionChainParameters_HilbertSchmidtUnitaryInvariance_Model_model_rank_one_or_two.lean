-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model.model_rank_one_or_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:35.998803+00:00
-- url     : https://prove2.me/submissions/8180eb0c-97e1-42aa-8ab7-bc3dfd6ed27a

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
theorem _root_.solution (u : Fin 20) : r0 u = 1 ∨ r0 u = 2 := by
  unfold r0; split_ifs <;> simp
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model
