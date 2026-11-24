-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.inclusion_matrix_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:45.843974+00:00
-- url     : https://prove2.me/submissions/0c238fd7-7c91-4f3b-b163-adcacf54f481

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ProjectiveLineModels
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates
namespace Formalism.LFunctionChainParameters.ProjectiveLineModels
theorem _root_.solution (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁] :
    (inclMat κ κ₁)ᴴ * inclMat κ κ₁ = 1 := by
  ext k l
  simp [inclMat, Matrix.mul_apply, Matrix.one_apply, eq_comm]
end Formalism.LFunctionChainParameters.ProjectiveLineModels
