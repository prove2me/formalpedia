-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.summable_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:33.044997+00:00
-- url     : https://prove2.me/submissions/4c623a86-525b-43f6-b313-d834ffa9677d

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic

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
theorem _root_.solution (f : τ → H₁) (hf : Summable (fun t => ‖f t‖)) :
    Summable (fun p : τ × τ => (inner ℂ (f p.1) (f p.2)).re) := by
  have h2 := Summable.mul_of_nonneg hf hf (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) h2)
  calc ‖(inner ℂ (f p.1) (f p.2)).re‖ ≤ ‖inner ℂ (f p.1) (f p.2)‖ := by
        rw [Real.norm_eq_abs]
        first
          | exact Complex.abs_re_le_norm _
          | exact Complex.abs_re_le_abs _
          | exact RCLike.abs_re_le_norm _
    _ ≤ ‖f p.1‖ * ‖f p.2‖ := norm_inner_le_norm _ _
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
