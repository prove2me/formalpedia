-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A2.domAfterA_of_old
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:34.859992+00:00
-- url     : https://prove2.me/submissions/22bfd164-c6d4-402a-b07f-44a45cf8401b

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_afterOfOldA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.P.BudgetLiftBounds Formalism.FourierDecayAlt.TC
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
theorem _root_.solution {E : Type} [Field E] [DecidableEq E] (D : Data E) (h : ThetaDomination D) :
    DomAfterA D := by
  exact (A1.afterOfOldA E D h).2
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
