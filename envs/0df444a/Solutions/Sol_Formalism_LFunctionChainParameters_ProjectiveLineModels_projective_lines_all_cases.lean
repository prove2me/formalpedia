-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.projective_lines_all_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:44:06.716271+00:00
-- url     : https://prove2.me/submissions/d523c910-289c-444f-ae2f-4caae9180db4

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_map_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_projective_lines_power_hypothesis

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
theorem _root_.solution : ModelLinesAll := by
  intro p _ hp19 K _ _ _ _ v
  obtain ⟨h, s, u, -, H⟩ := projective_lines_power_hypothesis p K hp19 v
  have hpR : (19 : ℝ) ≤ p := by exact_mod_cast hp19
  set HH : ℝ := |s - muMinDef (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1)
    (stdLat K (ZMod p × ZMod p))| + 1 with hHH
  have h0 : 0 < HH := by positivity
  refine ⟨h, s, u, u, HH, HH / ((p : ℝ) + 1), H HH u ?_ h0 le_rfl, ?_, line_map_ne_zero p K⟩
  · have := le_abs_self (s - muMinDef (Pi.basisFun K (ZMod p × ZMod p)) (fun _ => 1)
      (stdLat K (ZMod p × ZMod p)))
    linarith
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith
end Formalism.LFunctionChainParameters.ProjectiveLineModels
