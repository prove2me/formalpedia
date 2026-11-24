-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.one_level_inequality_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:52.237805+00:00
-- url     : https://prove2.me/submissions/526e1b9c-4152-4f07-8f0d-933ed5fbd1a1

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetLiftSquareRoot
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_oneLevelOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TA.OneLevelOfSteps := BudgetLiftBounds.oneLevelOfSteps
end Formalism.FourierDecayAlt.P
