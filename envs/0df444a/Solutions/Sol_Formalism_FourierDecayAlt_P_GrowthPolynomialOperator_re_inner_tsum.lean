-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.re_inner_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:58.405795+00:00
-- url     : https://prove2.me/submissions/49d0d5c3-9bf3-4cee-92f1-e779d7d8c975

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_cont_reInner

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
theorem _root_.solution (f : τ → H₁) (hf : Summable f) (w : H₁) :
    (inner ℂ w (∑' t, f t)).re = ∑' t, (inner ℂ w (f t)).re := by
  exact hf.map_tsum (reInner w) (cont_reInner w)
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
