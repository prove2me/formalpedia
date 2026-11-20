-- Prove2me | solution 1 for DeletionCode.DecoderExamples.fillFromBase_recovers_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:25.659198+00:00
-- url     : https://prove2.me/submissions/e1857d50-e8e6-4dca-bbea-f65ccf026e94

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    ((ConcreteFill.fillFromBase sampleWord 10 3 5 sampleMemory 5 0 1).bind
      (fun memory => (readBits memory 0 5).map (fun bits => List.ofFn bits))) =
      some [false, true, false, true, true] := by decide
end DeletionCode.DecoderExamples
