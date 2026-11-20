-- Prove2me | solution 1 for DeletionCode.DecoderExamples.seed_lookup_finds_position
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:24.683638+00:00
-- url     : https://prove2.me/submissions/3912e968-bbce-4566-98ab-3d8a87e2a6a1

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    SeedLookup.lookup sampleWord 10 3 5 1 sampleSeed = some 2 := by decide
end DeletionCode.DecoderExamples
