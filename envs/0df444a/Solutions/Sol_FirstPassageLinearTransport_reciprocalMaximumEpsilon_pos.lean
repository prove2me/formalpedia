-- Prove2me | solution 1 for FirstPassageLinearTransport.reciprocalMaximumEpsilon_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:16.350934+00:00
-- url     : https://prove2.me/submissions/64bfc9df-9753-4dd1-a18f-2d3012f995e5

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_two_thirds

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    0 < reciprocalMaximumEpsilon := by
  unfold reciprocalMaximumEpsilon
  have h : collatzTilt < 3 / 4 :=
    collatzTilt_lt_two_thirds.trans (by norm_num)
  linarith
end FirstPassageLinearTransport
