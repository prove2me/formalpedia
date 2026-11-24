-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.line_point_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:47.687048+00:00
-- url     : https://prove2.me/submissions/42ff14b6-922f-48a7-b4e3-470abf8130b9

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
theorem _root_.solution (i : Option (ZMod p) × ZMod p) : Function.Injective (linePt p i) := by
  rcases i with ⟨_ | m, b⟩ <;> intro t s h <;> simp [linePt] at h
  · exact h
  · exact h.1
end Formalism.LFunctionChainParameters.ProjectiveLineModels
