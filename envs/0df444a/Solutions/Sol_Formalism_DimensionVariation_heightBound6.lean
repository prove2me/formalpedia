-- Prove2me | solution 1 for Formalism.DimensionVariation.heightBound6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:44.901987+00:00
-- url     : https://prove2.me/submissions/611c1031-c568-4756-a370-1af1b6830c05

import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Theorems.Thm_Formalism_DimensionVariation_heightBound6_statement


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : HeightBound6 := heightBound6_statement
end Formalism.DimensionVariation
