-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ProjectiveLineModels.distinct_lines_gram_hs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:46:54.507807+00:00
-- url     : https://prove2.me/submissions/8f201e95-f05a-4864-a435-b146a3003fd8

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_distinct_lines_meet_at_most_once
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
theorem _root_.solution (i j : Option (ZMod p) × ZMod p) (hij : i ≠ j) :
    hsSq ((lineMat p i)ᴴ * lineMat p j) ≤ 1 := by
  have h : hsSq ((lineMat p i)ᴴ * lineMat p j)
      = (((Finset.univ : Finset (ZMod p × ZMod p)).filter
          (fun x => linePt p i x.1 = linePt p j x.2)).card : ℝ) := by
    rw [line_matrix_gram, Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
    simp [hsSq, apply_ite]
  rw [h]
  have : ((Finset.univ : Finset (ZMod p × ZMod p)).filter
      (fun x => linePt p i x.1 = linePt p j x.2)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha c hc
    rw [Finset.mem_filter] at ha hc
    obtain ⟨e1, e2⟩ := distinct_lines_meet_at_most_once p i j hij a.1 a.2 c.1 c.2 ha.2 hc.2
    exact Prod.ext e1 e2
  exact_mod_cast this
end Formalism.LFunctionChainParameters.ProjectiveLineModels
