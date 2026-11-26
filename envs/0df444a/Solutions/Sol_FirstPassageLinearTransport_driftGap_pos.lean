-- Prove2me | solution 1 for FirstPassageLinearTransport.driftGap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:10:36.217357+00:00
-- url     : https://prove2.me/submissions/b7de8cfe-71f1-49c1-9d7b-d9d5abd93e48

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_a0_lt_one

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution : 0 < driftGap := by
  unfold driftGap
  linarith [a0_lt_one]
end FirstPassageLinearTransport
