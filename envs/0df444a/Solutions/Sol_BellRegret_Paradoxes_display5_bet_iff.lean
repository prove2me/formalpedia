-- Prove2me | solution 1 for BellRegret.Paradoxes.display5_bet_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:42:46.445871+00:00
-- url     : https://prove2.me/submissions/8614cd48-9eb6-41d1-947f-6e39f55e2640

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem solution (f : ℝ → ℝ) (p : ℝ) :
    Prefers f (prob2 p) (horseBet p) horseNoBet ↔
      p * (f (1 - p) - f (p - 1)) > (1 - p) * (f p - f (-p)) := by
  simp only [Prefers, selectU, regretU, prob2, horseBet, horseNoBet, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring_nf
  constructor <;> intro h <;> linarith
