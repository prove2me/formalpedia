-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.top_inputs_of_shape_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:38.6948+00:00
-- url     : https://prove2.me/submissions/59a904b2-edb1-479a-aee2-cfb5bd3e7359

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_floor_height_le_height
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_restriction_lambda_antitone
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_restriction_lambda_antitone_kc
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_exact_exponents_fit_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLargePrime_holds
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_units_of_local_holds


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
theorem _root_.solution (hSW : ShapeWReal) : TopInputsReal := by
  intro P hH hL ι _ _ W hW l X hl hu hlJ ϖ n₀ e Λ L _ _ _ _ _ hwt hfin hϖ hA hT hS hI
  have hd := paramsLargePrime_holds P hH hL l hlJ
  have hsq : h0 P < l ^ 2 := by
    have h1 := hd.2.2.2.2.2.2.2
    have h2 := floor_height_le_height P hH
    have h3 : (0 : ℝ) ≤ (P.Nr : ℝ) := Nat.cast_nonneg _
    have h4 : (h0 P : ℝ) < (l : ℝ) ^ 2 := by linarith
    exact_mod_cast h4
  have ht : 1 ≤ P.t := by have := hH.t_ge; omega
  refine ⟨hl, RealLocalDeltaNabla.units_of_local_holds X.O l hl hu, hfin, hϖ, hsq, ht,
    fun τ hτ => hSW P hH hL ι W hW τ hτ, ?_, ?_, hA.1, hA.2, hT.1, hT.2, hS.1, hS.2, hI⟩
  · intro τ _ μ
    exact (exact_exponents_fit_holds l P.Nr (kc P) (W.lam τ) hl (restriction_lambda_antitone hW τ) (restriction_lambda_antitone_kc hW τ)).2 μ
  · intro τ
    exact (exact_exponents_fit_holds l P.Nr (kc P) (W.lam τ) hl (restriction_lambda_antitone hW τ) (restriction_lambda_antitone_kc hW τ)).1
end Formalism.CohomologicalDescent.ShortWeightBounds
