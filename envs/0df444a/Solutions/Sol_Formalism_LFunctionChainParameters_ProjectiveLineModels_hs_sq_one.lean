-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.hs_sq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:45.029731+00:00
-- url     : https://prove2.me/submissions/1e5ecbdd-cb6f-409d-ab5a-bf6700ab279f

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
theorem _root_.solution (n : Type) [Fintype n] [DecidableEq n] :
    hsSq (1 : Matrix n n ℂ) = Fintype.card n := by
  simp [hsSq, Matrix.one_apply, apply_ite]
end Formalism.LFunctionChainParameters.ProjectiveLineModels
