-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.summable_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:25.400312+00:00
-- url     : https://prove2.me/submissions/f1c04203-7024-4d31-a9f5-a6f63221d9c2

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
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Terms τ Rw I H H₁)
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution (hA : X.AbsConv) :
    Summable (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) := by
  have hA' : Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1 := hA
  have h2 := Summable.mul_of_nonneg hA'.2.1 hA'.2.1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_inner_le_norm _ _) h2
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
