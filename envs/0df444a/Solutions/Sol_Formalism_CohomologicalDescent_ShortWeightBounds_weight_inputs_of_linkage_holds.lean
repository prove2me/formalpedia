-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.weight_inputs_of_linkage_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:23:48.58374+00:00
-- url     : https://prove2.me/submissions/0a512f25-5aad-4e57-8d9b-71d7a878f402

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_first_input_of_link

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
theorem _root_.solution : WInputsOfLink := by
  intro P hH hL ι _ W hW l X hl hlJ h
  obtain ⟨ϖ, n₀, e, Λ, L, i1, i2, i3, i4, i5, hwt, hfin, hϖ, hA, hT, hS, hK⟩ := h
  exact ⟨ϖ, n₀, e, Λ, L, i1, i2, i3, i4, i5, hwt, hfin, hϖ, hA, hT, hS,
    first_input_of_link P hH hL ι W hW l X hl hlJ ϖ Λ L hwt hK⟩
end Formalism.CohomologicalDescent.ShortWeightBounds
