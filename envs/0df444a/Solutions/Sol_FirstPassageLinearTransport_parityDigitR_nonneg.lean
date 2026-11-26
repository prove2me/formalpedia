-- Prove2me | solution 1 for FirstPassageLinearTransport.parityDigitR_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:52.063804+00:00
-- url     : https://prove2.me/submissions/0ef0de1f-608c-4336-8f36-dbcadfeccbd9

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n i : ℕ) : 0 ≤ parityDigitR n i := by
  unfold parityDigitR
  positivity
end FirstPassageLinearTransport
