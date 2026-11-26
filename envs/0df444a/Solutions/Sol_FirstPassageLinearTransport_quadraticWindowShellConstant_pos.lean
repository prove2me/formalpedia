-- Prove2me | solution 1 for FirstPassageLinearTransport.quadraticWindowShellConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:25.951688+00:00
-- url     : https://prove2.me/submissions/e482d208-cee5-4412-bca7-48c92c8ccb33

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    0 < quadraticWindowShellConstant := by
  unfold quadraticWindowShellConstant
  positivity
end FirstPassageLinearTransport
