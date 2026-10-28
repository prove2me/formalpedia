-- Prove2me | solution 1 for BitDFT.vector_encoding_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:02:44.215716+00:00
-- url     : https://prove2.me/submissions/b0ef92e5-8c85-477e-863d-9819bb68219b

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
noncomputable section
open BitDFT

theorem solution {n : ℕ} (w : ℕ) (U : Fin n → ℤ × ℤ) :
    (encVector w U).length = 2 * n * (w + 1) := by
  simp [encVector, encComplex, encInt, IntMul.bin, List.length_flatMap,
    List.map_const', List.sum_replicate_nat, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_add] <;> ring

#print axioms solution
