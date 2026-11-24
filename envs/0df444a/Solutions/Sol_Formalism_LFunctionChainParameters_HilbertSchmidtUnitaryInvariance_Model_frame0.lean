-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model.frame0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:28:39.545159+00:00
-- url     : https://prove2.me/submissions/3b9d947b-a69d-4880-be65-e1a2867d32b3

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
theorem _root_.solution : OrthFrame J0 modelEmbedding := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [J0, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i; fin_cases j; simp [modelEmbedding, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J0, modelEmbedding, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.Model
