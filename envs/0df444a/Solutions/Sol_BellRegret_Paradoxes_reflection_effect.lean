-- Prove2me | solution 1 for BellRegret.Paradoxes.reflection_effect
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:42:49.516993+00:00
-- url     : https://prove2.me/submissions/72b8df51-e18e-4467-83bb-e98a9088ed00

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem solution (f : ℝ → ℝ) (p x₁ x₂ x₃ : ℝ) :
    Indiff f (prob2 p) ![x₂, x₂] ![x₁, x₃] ↔
      Indiff f (prob2 p) ![-x₂, -x₂] ![-x₁, -x₃] := by
  simp only [Indiff, selectU, regretU, prob2, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring_nf
  constructor <;> intro h <;> linarith
