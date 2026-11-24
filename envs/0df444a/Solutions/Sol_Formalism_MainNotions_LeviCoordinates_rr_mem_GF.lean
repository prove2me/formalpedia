-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_mem_GF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:08:26.973409+00:00
-- url     : https://prove2.me/submissions/fd36d780-e664-4472-8ecc-94f9e9a472ed

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
theorem _root_.solution (I : AutInst) (x : I.GA) : x ∈ rr_GF I ↔ x ∈ I.GFset := Iff.rfl
end Formalism.MainNotions.LeviCoordinates
