-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.weight_lt_lower_translation_of_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:27.143294+00:00
-- url     : https://prove2.me/submissions/e3d4c73a-b730-4f1b-a155-3618f86ad0ee

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_abs_weight_sub_near_translation_le
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_two_eta_lt_b
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_eta_nonneg__1aa77f39dc77


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
theorem _root_.solution (P : Par) (hP : P.Hyp) (hL : P.Large) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι)
    (hτ : τ ∈ W.T2) (a : ℕ) (h1 : kc P ≤ a) (h2 : a < P.Nr) : W.U P τ a < W.xm τ := by
  have h3 := abs_weight_sub_near_translation_le P hP W hW τ a h1 h2
  have h4 := (hW.thick τ hτ).1.1
  have h5 := two_eta_lt_b P hP hL
  have h6 := (hW.window τ).1
  have h7 := eta_nonneg' hP
  have h8 := (abs_le.mp h3).2
  have : (W.U P τ a : ℝ) < (W.xm τ : ℝ) := by linarith
  exact_mod_cast this
end Formalism.CohomologicalDescent.ShortWeightBounds
