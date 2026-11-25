-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.inclusion_w_of_shape_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:51:17.694455+00:00
-- url     : https://prove2.me/submissions/85f79d6b-c75e-436a-b2aa-77d9d5a3d750

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_theorem_w_top_short_bound_holds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_top_inputs_of_shape_w
import Theorems.Thm_Formalism_CohomologicalDescent_LD_last_graded_of_graded_alone


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
theorem _root_.solution (hSW : ShapeWReal) : InclWReal := by
  intro hD P hH hL ι _ _ W hW l X hl hu hlJ hWI
  obtain ⟨ϖ, n₀, e, Λ, L, _, _, _, _, _, hwt, hfin, hϖ, hA, hT, hS, hI⟩ := hWI
  have hTop := top_inputs_of_shape_w hSW P hH hL ι W hW l X hl hu hlJ ϖ n₀ e Λ L hwt hfin hϖ hA hT hS hI
  have h := theorem_w_top_short_bound_holds (last_graded_of_graded_alone hD) X.O X.A X.G X.Γ X.K X.jK ι l
    P.Nr (kc P) P.t (h0 P) W.lam W.T2 W.j W.q W.xm W.xp (fun τ => W.ecl P τ l)
    (fun τ => W.ex P τ l) (W.iW P l) X.T X.S ϖ n₀ e Λ L hwt hTop
  exact h
end Formalism.CohomologicalDescent.ShortWeightBounds
