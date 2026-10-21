-- Prove2me | solution 1 for BellRegret.Paradoxes.probabilistic_insurance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:44:12.921548+00:00
-- url     : https://prove2.me/submissions/858dd5d8-9e93-4be5-ba6c-fb10f7c7afcb

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem solution (f : ℝ → ℝ) (p q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hind : Indiff f (prob3 q) (fullInsurance p) selfInsurance) :
    (f (p / 2) - f (-p / 2) < 1 / 2 * (f p - f (-p)) ↔
      Prefers f (prob3 q) (fullInsurance p) (probInsurance p)) ∧
    (f (p / 2) - f (-p / 2) < 1 / 2 * (f p - f (-p)) ↔
      Prefers f (prob3 q) (probInsurance p) selfInsurance) := by
  have hq : 0 < 1 - q := by linarith
  simp only [Indiff, selectU, regretU, prob3, fullInsurance, selfInsurance, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hind
  simp only [Prefers, selectU, regretU, prob3, fullInsurance, selfInsurance, probInsurance,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring_nf at hind ⊢
  constructor
  · constructor
    · intro h
      nlinarith
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith
  · constructor
    · intro h
      nlinarith
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith
