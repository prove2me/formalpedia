-- Prove2me | solution 1 for GapCVP.Comparator.encodeBinaryNearestCodewordInstance_eq_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/b1b00f13-3250-4f61-82d8-28652b8a5179

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
theorem _root_.solution
    (record : BinaryNearestCodewordInstance) :
    encodeBinaryNearestCodewordInstance record =
      GapCVP.Factor400BinaryDecodingPromiseReduction.encodeBinaryNearestCodewordInstance
        (toOriginalNearest record) := rfl
end GapCVP.Comparator
