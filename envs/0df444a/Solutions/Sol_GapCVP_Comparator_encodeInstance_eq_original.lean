-- Prove2me | solution 1 for GapCVP.Comparator.encodeInstance_eq_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/39699ac6-6db7-4e1d-9358-d9523e14bfd8

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
theorem _root_.solution (I : Instance) :
    encodeInstance I =
      GapCVP.BinaryEncoding.encodeGapCVPInstance
        (toOriginal I) := rfl
end GapCVP.Comparator
