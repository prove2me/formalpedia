-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzThreeBlockEnvelopeIndicator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:44.268074+00:00
-- url     : https://prove2.me/submissions/ca0be74f-879b-4d14-953b-4edd20eb3a00

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {a b : ℕ} (B q : ℝ)
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool) :
    0 ≤ collatzThreeBlockEnvelopeIndicator B q u v w := by
  classical
  unfold collatzThreeBlockEnvelopeIndicator
  split <;> norm_num
end FirstPassageLinearTransport
