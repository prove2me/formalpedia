-- Prove2me | solution 1 for DeletionCode.DecoderExamples.crossing_transfer_uses_extension_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:49.746503+00:00
-- url     : https://prove2.me/submissions/0334fa0f-b380-46f7-9154-a92b868fb244

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
    (result.1, List.ofFn result.2) = (5, [false]) := by decide
end DeletionCode.DecoderExamples
