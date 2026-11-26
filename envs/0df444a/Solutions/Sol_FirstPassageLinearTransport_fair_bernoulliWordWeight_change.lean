-- Prove2me | solution 1 for FirstPassageLinearTransport.fair_bernoulliWordWeight_change
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:01.522494+00:00
-- url     : https://prove2.me/submissions/a541e02e-1815-429a-ad6b-6b4d4b7050da

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_fair_word_weight_change
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_half_eq

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {m : ℕ} (v : Fin m → Bool) :
    bernoulliWordWeight (1 / 2) v =
      bernoulliWordWeight collatzTilt v *
        Real.exp (-(collatzFairTiltRate * (m : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement v) := by
  rw [bernoulliWordWeight_half_eq]
  exact fair_word_weight_change v
end FirstPassageLinearTransport
