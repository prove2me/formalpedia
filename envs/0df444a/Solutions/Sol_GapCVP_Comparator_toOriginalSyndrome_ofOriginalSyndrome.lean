-- Prove2me | solution 1 for GapCVP.Comparator.toOriginalSyndrome_ofOriginalSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/400bb6e0-b454-4432-87fc-8ad84160fdb1

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
    (record : GapCVP.Factor400BinaryDecodingPromiseReduction.BinarySyndromeDecodingInstance) :
    toOriginalSyndrome (ofOriginalSyndrome record) = record := rfl
end GapCVP.Comparator
