-- Prove2me | solution 1 for DeletionCode.DecoderExamples.checked_write_rejects_out_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:27.417513+00:00
-- url     : https://prove2.me/submissions/fe424309-80b8-446e-a6c9-b6153a4870cf

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    (writeBits empty 5 4 sampleSeed).isNone = true := by decide
end DeletionCode.DecoderExamples
