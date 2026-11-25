-- Prove2me | solution 1 for Formalism.DimensionVariation.divIneqExplicit6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:40.761333+00:00
-- url     : https://prove2.me/submissions/713e0a25-88fd-4562-85b7-9a1b544db062

import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Theorems.Thm_Formalism_DimensionVariation_division_inequality_explicit


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
theorem _root_.solution : DivIneqExplicit6 := division_inequality_explicit
end Formalism.DimensionVariation
