-- Prove2me | solution 1 for FatkhullinPolyak.Discrete.trace_duality_lyapunov
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:41:31.136423+00:00
-- url     : https://prove2.me/submissions/4eef2d06-da26-4169-8f63-8375fad89687

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

theorem aux_tdl_main {n : ℕ} (A X Y W V : Matrix (Fin n) (Fin n) ℝ)
    (hX : A.transpose * X + X * A + W = 0)
    (hY : A * Y + Y * A.transpose + V = 0) :
    Matrix.trace (X * V) = Matrix.trace (Y * W) := by
  have hW : W = -(A.transpose * X + X * A) := eq_neg_of_add_eq_zero_right hX
  have hV : V = -(A * Y + Y * A.transpose) := eq_neg_of_add_eq_zero_right hY
  subst hW hV
  simp only [Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_add, Matrix.trace_add, neg_inj]
  have h1 : Matrix.trace (X * (A * Y)) = Matrix.trace (Y * (X * A)) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h2 : Matrix.trace (X * (Y * A.transpose)) = Matrix.trace (Y * (A.transpose * X)) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [h1, h2, add_comm]

end FatkhullinPolyak.Discrete

open FatkhullinPolyak.Discrete

theorem solution {n : ℕ} (A X Y W V : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsHurwitz A)
    (hX : A.transpose * X + X * A + W = 0)
    (hY : A * Y + Y * A.transpose + V = 0) :
    Matrix.trace (X * V) = Matrix.trace (Y * W) :=
  aux_tdl_main A X Y W V hX hY
