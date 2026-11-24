-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.line_matrix_gram_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:48:02.914345+00:00
-- url     : https://prove2.me/submissions/b29b3460-3b57-498a-b3e1-5cb39bdd7b97

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_point_injective
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_matrix_gram

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
theorem _root_.solution (i : Option (ZMod p) × ZMod p) : (lineMat p i)ᴴ * lineMat p i = 1 := by
  rw [line_matrix_gram]
  ext t t'
  simp [Matrix.one_apply, (line_point_injective p i).eq_iff]
end Formalism.LFunctionChainParameters.ProjectiveLineModels
