-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.line_rank_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:48.594796+00:00
-- url     : https://prove2.me/submissions/bec741bb-fe27-4a6f-8c8a-70751d074138

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
variable (p : ℕ) [Fact p.Prime]
namespace Formalism.LFunctionChainParameters.ProjectiveLineModels
theorem _root_.solution : RsG (fun _ : Option (ZMod p) × ZMod p => ZMod p) = (p : ℝ) ^ 2 * ((p : ℝ) + 1) := by
  simp [RsG, ZMod.card]
  ring
end Formalism.LFunctionChainParameters.ProjectiveLineModels
