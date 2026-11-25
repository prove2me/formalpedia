-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.projective_lines_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:30.116873+00:00
-- url     : https://prove2.me/submissions/11e30de8-cb09-4332-838e-a62df1244369

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_projective_lines_all_cases

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
theorem _root_.solution : ModelLines := by
  intro K _ _ _ _ v
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨h, s, u, U, HH, bb, H, h1, h2⟩ := projective_lines_all_cases 19 le_rfl K v
  have e1 : ((19 : ℕ) : ℝ) ^ 2 = 361 := by norm_num
  have e2 : ((19 : ℕ) : ℝ) + 1 = 20 := by norm_num
  rw [e1, e2] at H
  exact ⟨h, s, u, U, HH, bb, H, h1, h2⟩
end Formalism.LFunctionChainParameters.ProjectiveLineModels
