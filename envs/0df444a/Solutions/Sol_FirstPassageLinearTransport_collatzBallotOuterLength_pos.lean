-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzBallotOuterLength_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:55.061751+00:00
-- url     : https://prove2.me/submissions/e4724dc0-a390-40c4-bb53-4c4e17cee539

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {m : ℕ} (hm : 8 ≤ m) :
    0 < collatzBallotOuterLength m := by
  unfold collatzBallotOuterLength
  omega
end FirstPassageLinearTransport
