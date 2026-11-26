-- Prove2me | solution 1 for FirstPassageLinearTransport.sum_weightedSurvivalFactor_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:08.631746+00:00
-- url     : https://prove2.me/submissions/0ee80056-8df2-4b9b-a1e4-4fb48d96ad12

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (p : ℝ) (x : Bool → ℝ) (lo z : ℝ) (r : ℕ) :
    ∑ v : Fin r → Bool, weightedSurvivalFactor p x lo z v =
      weightedSurvivalWordMass p x lo r z := by
  classical
  unfold weightedSurvivalFactor wordSurvivalIndicator weightedSurvivalWordMass
  rfl
end FirstPassageLinearTransport
