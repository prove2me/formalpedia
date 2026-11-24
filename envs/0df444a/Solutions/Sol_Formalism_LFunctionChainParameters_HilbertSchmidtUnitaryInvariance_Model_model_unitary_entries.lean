-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model.model_unitary_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:37.268174+00:00
-- url     : https://prove2.me/submissions/001f910a-0bbc-476f-910c-c4329a0eb879

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
theorem _root_.solution (u : Fin 20) : IsUni (U0 u) := by
  constructor <;> simp [U0, Matrix.conjTranspose_smul, smul_smul]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model
