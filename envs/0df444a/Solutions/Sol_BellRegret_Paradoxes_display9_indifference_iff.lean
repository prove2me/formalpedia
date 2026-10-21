-- Prove2me | solution 1 for BellRegret.Paradoxes.display9_indifference_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:42:48.27955+00:00
-- url     : https://prove2.me/submissions/4b56c4b3-e501-4a1f-b075-1fcef3ef8e47

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem solution (f : ℝ → ℝ) (p q : ℝ) :
    Indiff f (prob3 q) (fullInsurance p) selfInsurance ↔
      -q + (1 - q) * (f p - f (-p)) = -p + q * (f (1 - p) - f (p - 1)) := by
  simp only [Indiff, selectU, regretU, prob3, fullInsurance, selfInsurance, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring_nf
  constructor <;> intro h <;> linarith
