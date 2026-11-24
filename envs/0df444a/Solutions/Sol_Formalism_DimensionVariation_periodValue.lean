-- Prove2me | solution 1 for Formalism.DimensionVariation.periodValue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:12.147969+00:00
-- url     : https://prove2.me/submissions/10d7c2cf-da92-492b-ada7-1eef94279f2d

import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_Assembly
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_ClassSchur
import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementD
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_DominanceMono
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GaussCoord
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementE
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Theorems.Thm_Formalism_DimensionVariation_period_value


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution : PeriodValue := period_value
end Formalism.DimensionVariation
