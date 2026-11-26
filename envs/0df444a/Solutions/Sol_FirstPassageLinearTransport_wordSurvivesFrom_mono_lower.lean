-- Prove2me | solution 1 for FirstPassageLinearTransport.wordSurvivesFrom_mono_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:36.16409+00:00
-- url     : https://prove2.me/submissions/aee036f5-82ee-45b2-9e72-a47506a828e8

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lo lo' : ℝ} {increment : Bool → ℝ} {r : ℕ} {z : ℝ}
    {v : Fin r → Bool} (hlo : lo' ≤ lo)
    (h : wordSurvivesFrom lo increment r z v) :
    wordSurvivesFrom lo' increment r z v := by
  induction r generalizing z with
  | zero =>
      exact hlo.trans h
  | succ r ih =>
      exact ⟨hlo.trans h.1, ih h.2⟩
end FirstPassageLinearTransport
