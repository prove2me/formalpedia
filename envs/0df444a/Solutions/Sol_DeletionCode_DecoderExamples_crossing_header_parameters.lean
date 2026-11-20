-- Prove2me | solution 1 for DeletionCode.DecoderExamples.crossing_header_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:49.180155+00:00
-- url     : https://prove2.me/submissions/1e185555-91e9-4704-a6c7-035c5889c3e8

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_DecoderExamples

set_option autoImplicit true
open DeletionCode DeletionCode.DecoderExamples
open Windows PartialWords
namespace DeletionCode.DecoderExamples
theorem _root_.solution :
    1 ≤ crossingHeader.rho ∧ crossingHeader.rho ≤ 1 + 1 ∧
      HeaderRecovery.windowLength 1 = 6 ∧
      crossingLong (HeaderRecovery.editOffset 1) = crossingHeader.bit := by decide
end DeletionCode.DecoderExamples
