-- Prove2me | solution 1 for GapCVP.Comparator.toOriginal_ofOriginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/7297b3fa-f8f1-4e44-82ba-ba2c8632035c

import Mathlib
import Definitions.Def_GapCVP

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
noncomputable section
open scoped BigOperators
open GapCVP.Comparator
namespace GapCVP.Comparator
theorem _root_.solution (I : GapCVP.GapCVPInstance) :
    toOriginal (ofOriginal I) = I := rfl
end GapCVP.Comparator
