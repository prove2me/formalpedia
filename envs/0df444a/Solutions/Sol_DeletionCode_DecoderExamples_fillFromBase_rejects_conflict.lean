-- Prove2me | solution 1 for DeletionCode.DecoderExamples.fillFromBase_rejects_conflict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:26.205873+00:00
-- url     : https://prove2.me/submissions/c98005de-307c-4fb9-9f38-f88ecfcceb9e

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    (ConcreteFill.fillFromBase sampleWord 10 3 5
      (putBits sampleMemory 0 (fun _ : Fin 1 => true)) 5 0 1).isNone = true := by decide
end DeletionCode.DecoderExamples
