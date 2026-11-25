-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.shape_w_real_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:23.143213+00:00
-- url     : https://prove2.me/submissions/cda601d0-ad61-4cd3-becf-dfe089133b83

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_ShortWeightBounds_weight_nonneg__27470cb891f0
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_weight_lt_lower_translation_of_thick
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_upper_translation_le_floor_height
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_weight_le_upper_translation_of_thick

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
theorem _root_.solution : ShapeWReal := by
  intro P hP hL ι W hW τ hτ
  have hr := rank_fits_block_and_t_ge_six P hP W hW τ
  have hx := upper_translation_le_floor_height P hP W hW τ hτ
  refine ⟨hW.what₂ τ, hW.anti τ, hW.block τ, ?_, hW.cloud τ, ?_, ?_, (hW.window τ).2.1, ?_⟩
  · have h1 := weight_le_upper_translation_of_thick P hP hL W hW τ hτ 0 (by omega)
    unfold Wts.U UN at h1
    omega
  · intro a h1 h2
    exact weight_lt_lower_translation_of_thick P hP hL W hW τ hτ a h1 (by omega)
  · exact weight_lt_lower_translation_of_thick P hP hL W hW τ hτ _ (by omega) (by omega)
  · have h1 := weight_nonneg' P W τ (kc P + W.j τ) (by omega)
    unfold Wts.U at h1
    omega
end Formalism.CohomologicalDescent.ShortWeightBounds
