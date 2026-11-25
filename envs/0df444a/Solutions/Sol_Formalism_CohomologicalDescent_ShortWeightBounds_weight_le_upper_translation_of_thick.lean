-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.weight_le_upper_translation_of_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:45.168613+00:00
-- url     : https://prove2.me/submissions/7d3b5497-b14d-4f03-bcb3-c09f47c2aa91

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
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
theorem _root_.solution (P : Par) (hP : P.Hyp) (hL : P.Large) {ι : Type} (W : Wts ι) (hW : W.Ok P)
    (τ : ι) (hτ : τ ∈ W.T2) (a : ℕ) (h2 : a < P.Nr) : W.U P τ a ≤ W.xp τ := by
  by_cases h : a < kc P
  · exact (hW.cloud τ a h).2
  · have h1 := weight_lt_lower_translation_of_thick P hP hL W hW τ hτ a (by omega) h2
    have h3 := (hW.window τ).2.1
    omega
end Formalism.CohomologicalDescent.ShortWeightBounds
