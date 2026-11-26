-- Prove2me | solution 1 for FirstPassageLinearTransport.wordSurvivalIndicator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:52.311298+00:00
-- url     : https://prove2.me/submissions/56f1d44c-f391-40ec-88af-c1791572b5b4

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r : ℕ} (lo : ℝ) (x : Bool → ℝ) (z : ℝ) (v : Fin r → Bool) :
    0 ≤ wordSurvivalIndicator lo x z v := by
  classical
  unfold wordSurvivalIndicator
  split <;> norm_num
end FirstPassageLinearTransport
