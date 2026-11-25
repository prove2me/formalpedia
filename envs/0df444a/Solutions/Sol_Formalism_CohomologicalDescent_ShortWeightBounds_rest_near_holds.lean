-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.rest_near_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:25:09.203709+00:00
-- url     : https://prove2.me/submissions/92fbd592-a2bc-4ab5-80bd-4c692704125b

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_weights_strictAnti
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_j_add_q_eq_m
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_abs_weight_sub_near_translation_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
namespace Formalism.CohomologicalDescent.ShortWeightBounds
theorem _root_.solution : RestNear := by
  intro P hP ι W hW τ
  exact ⟨fun a h1 h2 => abs_weight_sub_near_translation_le P hP W hW τ a h1 h2, fun a h1 h2 => weight_on_block_eq_bot_add P hP W hW τ a h1 h2,
    top_eq_bot_add_t_sub_one P hP W hW τ, j_add_q_eq_m P hP W hW τ, fun a b h1 h2 => weights_strictAnti P W hW τ a b h1 h2⟩
end Formalism.CohomologicalDescent.ShortWeightBounds
