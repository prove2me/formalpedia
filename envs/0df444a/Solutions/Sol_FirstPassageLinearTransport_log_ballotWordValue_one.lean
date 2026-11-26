-- Prove2me | solution 1 for FirstPassageLinearTransport.log_ballotWordValue_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:17.70737+00:00
-- url     : https://prove2.me/submissions/8bb35434-180a-4682-884c-b317d43b8e49

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_collatz
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_one_eq_exp_incrementSum

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r : ℕ} (v : Fin r → Bool) :
    Real.log (ballotWordValue 1 v) =
      ((boolSupport v).card : ℝ) * Real.log 3 -
        (r : ℝ) * Real.log 2 := by
  rw [ballotWordValue_one_eq_exp_incrementSum, Real.log_exp,
    wordIncrementSum_collatz]
end FirstPassageLinearTransport
