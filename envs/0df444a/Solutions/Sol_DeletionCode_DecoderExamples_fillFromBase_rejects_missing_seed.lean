-- Prove2me | solution 1 for DeletionCode.DecoderExamples.fillFromBase_rejects_missing_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:48.718671+00:00
-- url     : https://prove2.me/submissions/2d4d28ac-3871-4a12-abae-af3538cce503

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    (ConcreteFill.fillFromBase sampleWord 10 3 5 empty 5 0 1).isNone = true := by decide
end DeletionCode.DecoderExamples
