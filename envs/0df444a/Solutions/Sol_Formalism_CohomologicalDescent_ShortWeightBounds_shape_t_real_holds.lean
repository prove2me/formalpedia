-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.shape_t_real_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:20:16.548258+00:00
-- url     : https://prove2.me/submissions/15c19869-f5a3-4182-a7f6-878a95766086

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_j_add_q_eq_m
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_ShortWeightBounds_weight_nonneg__27470cb891f0
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_weight_lt_lower_translation_of_thick

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
theorem _root_.solution : ShapeTReal := by
  intro P hP hL ι W hW J τ hτ
  have hτ' : τ ∈ W.T2 := hτ
  have hr := rank_fits_block_and_t_ge_six P hP W hW τ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact weight_nonneg' P W τ _ (by omega)
  · exact weight_lt_lower_translation_of_thick P hP hL W hW τ hτ' _ (by omega) (by omega)
  · exact (hW.window τ).2.1
  · exact (hW.thick τ hτ').2
  · have h1 := (hW.window τ).1
    have h2 := (hW.window τ).2.2
    show ((W.xp τ - W.xm τ : ℤ) : ℝ) ≤ P.S
    push_cast
    linarith
  · have := j_add_q_eq_m P hP W hW τ
    show W.q τ + W.j τ ≤ P.m
    omega
end Formalism.CohomologicalDescent.ShortWeightBounds
