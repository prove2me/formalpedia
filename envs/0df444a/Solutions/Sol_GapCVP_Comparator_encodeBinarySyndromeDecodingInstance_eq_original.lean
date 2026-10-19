-- Prove2me | solution 1 for GapCVP.Comparator.encodeBinarySyndromeDecodingInstance_eq_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/95d1b38c-264d-4a8a-b9fc-7c8a79db07a4

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
    (record : BinarySyndromeDecodingInstance) :
    encodeBinarySyndromeDecodingInstance record =
      GapCVP.Factor400BinaryDecodingPromiseReduction.encodeBinarySyndromeDecodingInstance
        (toOriginalSyndrome record) := rfl
end GapCVP.Comparator
