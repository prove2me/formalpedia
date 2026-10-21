-- Prove2me | solution 1 for BellRegret.Paradoxes.display6_insurance_iff_bet
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:42:47.328055+00:00
-- url     : https://prove2.me/submissions/1e3ba679-98b6-42de-afb1-0e2a46c733ba

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem solution (f : ℝ → ℝ) (p : ℝ) :
    (Prefers f (prob2 p) (carInsure p) carNoInsure ↔
      p * (f (1 - p) - f (p - 1)) > (1 - p) * (f p - f (-p))) ∧
    (Prefers f (prob2 p) (carInsure p) carNoInsure ↔
      Prefers f (prob2 p) (horseBet p) horseNoBet) := by
  have h1 : Prefers f (prob2 p) (carInsure p) carNoInsure ↔
      p * (f (1 - p) - f (p - 1)) > (1 - p) * (f p - f (-p)) := by
    simp only [Prefers, selectU, regretU, prob2, carInsure, carNoInsure, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    constructor <;> intro h <;> linarith
  have h2 : Prefers f (prob2 p) (horseBet p) horseNoBet ↔
      p * (f (1 - p) - f (p - 1)) > (1 - p) * (f p - f (-p)) := by
    simp only [Prefers, selectU, regretU, prob2, horseBet, horseNoBet, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    constructor <;> intro h <;> linarith
  exact ⟨h1, h1.trans h2.symm⟩
