-- Prove2me | solution 1 for DeletionCode.DecoderExamples.seed_lookup_recovers_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:25.067932+00:00
-- url     : https://prove2.me/submissions/b1cd206b-811d-414b-8b4b-29218d5be9ce

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    (SeedLookup.recoverWindow sampleWord 10 3 5 1 sampleSeed).map
      (fun bits => List.ofFn bits) = some [false, true, false, true, true] := by decide
end DeletionCode.DecoderExamples
