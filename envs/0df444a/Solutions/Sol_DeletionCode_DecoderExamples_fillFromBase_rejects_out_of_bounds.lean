-- Prove2me | solution 1 for DeletionCode.DecoderExamples.fillFromBase_rejects_out_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:48.234183+00:00
-- url     : https://prove2.me/submissions/e0623ccd-5970-46e5-8c66-8d1c03236537

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    (ConcreteFill.fillFromBase sampleWord 10 3 5 sampleMemory 4 0 1).isNone = true :=
  by decide
end DeletionCode.DecoderExamples
