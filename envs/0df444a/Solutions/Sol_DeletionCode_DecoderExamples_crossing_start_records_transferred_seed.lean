-- Prove2me | solution 1 for DeletionCode.DecoderExamples.crossing_start_records_transferred_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:50.72419+00:00
-- url     : https://prove2.me/submissions/151821de-1e56-43a4-8629-b3f4ca4564a0

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    ((ConcreteStart.startPositive 1 crossingHeader 5 (fun _ : Fin 1 => true) false empty).bind
      (fun memory => (readBits memory 5 1).map (fun bits => List.ofFn bits))) =
      some [false] := by decide
end DeletionCode.DecoderExamples
