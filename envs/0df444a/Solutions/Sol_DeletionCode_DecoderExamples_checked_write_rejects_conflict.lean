-- Prove2me | solution 1 for DeletionCode.DecoderExamples.checked_write_rejects_conflict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:26.824059+00:00
-- url     : https://prove2.me/submissions/55cc9c5f-d2ac-4a3b-b52a-bf017fe289ca

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    (writeBits (putBits empty 0 (fun _ : Fin 1 => false)) 5 0
      (fun _ : Fin 1 => true)).isNone = true := by decide
end DeletionCode.DecoderExamples
