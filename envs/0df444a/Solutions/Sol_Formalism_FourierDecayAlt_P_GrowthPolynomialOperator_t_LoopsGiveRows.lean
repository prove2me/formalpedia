-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_LoopsGiveRows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.363984+00:00
-- url     : https://prove2.me/submissions/4087e708-38d1-455b-8ff0-4072548074ee

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
theorem _root_.solution : LoopsGiveRows := by
  intro hSF τ Rw I H H₁ _ _ _ _ _ X ε dd hA hL
  have hL' : X.pairAbs (X.big X.nzSet ∪ X.nsc X.genSet) ≤ ε * dd := hL
  constructor
  · show X.pairAbs (X.big X.nzSet) ≤ ε * dd
    exact ((hSF τ Rw I H H₁ X hA _ _ Set.subset_union_left).1).trans hL'
  · show X.pairAbs (X.nsc X.genSet) ≤ ε * dd
    exact ((hSF τ Rw I H H₁ X hA _ _ Set.subset_union_right).1).trans hL'
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
