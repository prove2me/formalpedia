-- Prove2me | solution 1 for FirstPassageLinearTransport.reciprocalMaximumConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:14.737189+00:00
-- url     : https://prove2.me/submissions/ac117871-d1bd-411a-bd49-89725a6aa00b

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_reciprocalMaximumEpsilon_pos

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    0 < reciprocalMaximumConstant := by
  unfold reciprocalMaximumConstant
  have hsquare : 0 < reciprocalMaximumEpsilon ^ 2 :=
    sq_pos_of_pos reciprocalMaximumEpsilon_pos
  exact div_pos (by norm_num) (mul_pos (by norm_num) hsquare)
end FirstPassageLinearTransport
