-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.reduction_bound_of_one_level
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:53.441351+00:00
-- url     : https://prove2.me/submissions/c7077592-4c02-4550-b814-2c522b18b15a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetLiftSquareRoot
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_reductionOfSteps

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
theorem _root_.solution : Formalism.FourierDecayAlt.TA.ReductionOfSteps := BudgetLiftBounds.reductionOfSteps
end Formalism.FourierDecayAlt.P
