-- Prove2me | solution 1 for DeletionCode.DecoderExamples.crossing_transfer_agrees_with_negative_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:50.292168+00:00
-- url     : https://prove2.me/submissions/86c22703-622b-4e87-a917-707695ed9e20

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    let result := HeaderRecovery.transferFinite 1 crossingHeader 5
      (fun _ : Fin 1 => true) false
    List.ofFn result.2 = List.ofFn (fun i : Fin 1 =>
      HeaderRecovery.negativePath 1 crossingHeader crossingLong (result.1 + i.val)) :=
  by decide
end DeletionCode.DecoderExamples
