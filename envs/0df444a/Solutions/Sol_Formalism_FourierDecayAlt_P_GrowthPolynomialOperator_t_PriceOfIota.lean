-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_PriceOfIota
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:34.979894+00:00
-- url     : https://prove2.me/submissions/b765f964-a10f-427f-9811-6d4f80ec02f9

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
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : NormSqBoundOfEqualIota := by
  intro hEI τ Rw I H H₁ _ _ _ _ _ X Pg S hN hG
  have hN' : ‖X.part S‖ ^ 2 =
      (∑ i, ∑ j, X.GG i j * inner ℂ (X.vecPart S i) (X.vecPart S j)).re := hN
  have h := hEI I H₁ X.GG (Pg * X.Gam1) (X.vecPart S) hG
  show ‖X.part S‖ ^ 2 ≤ Pg * (X.Gam1 * ∑ i, ‖X.vecPart S i‖ ^ 2)
  rw [hN']
  calc _ ≤ (Pg * X.Gam1) * ∑ i, ‖X.vecPart S i‖ ^ 2 := h
    _ = Pg * (X.Gam1 * ∑ i, ‖X.vecPart S i‖ ^ 2) := by ring
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
