-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_GF_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:52:36.785913+00:00
-- url     : https://prove2.me/submissions/02b7e7c7-73ed-4f8e-9c8f-4edc99dfdeba

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrgCountableField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (I : AutInst) : ((rr_GF I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl
end Formalism.MainNotions.LeviCoordinates
