-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.norm_sq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:59.446147+00:00
-- url     : https://prove2.me/submissions/e08d6cf2-e2cc-4a3c-bfca-d1ffcd80f812

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_re_inner_tsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_summable_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
open Classical
variable {τ H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution [CompleteSpace H₁] (f : τ → H₁) (hf : Summable (fun t => ‖f t‖)) :
    ‖∑' t, f t‖ ^ 2 = ∑' p : τ × τ, (inner ℂ (f p.1) (f p.2)).re := by
  have hs : Summable f := Summable.of_norm hf
  have h1 : ‖∑' t, f t‖ ^ 2 = (inner ℂ (∑' t, f t) (∑' t, f t)).re := by
    first
      | exact norm_sq_eq_re_inner (𝕜 := ℂ) _
      | exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
  have h2 : ∀ b, (inner ℂ (∑' t, f t) (f b)).re = ∑' a, (inner ℂ (f b) (f a)).re := by
    intro b
    rw [← inner_conj_symm, Complex.conj_re]
    exact re_inner_tsum f hs (f b)
  rw [h1, re_inner_tsum f hs (∑' t, f t)]
  simp_rw [h2]
  have hg := summable_re f hf
  first
    | exact (Summable.tsum_prod hg).symm
    | exact (tsum_prod' hg (fun b => hg.prod_factor b)).symm
    | exact (Summable.tsum_prod' hg (fun b => hg.prod_factor b)).symm
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
