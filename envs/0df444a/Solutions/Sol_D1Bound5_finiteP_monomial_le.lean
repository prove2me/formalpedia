-- Prove2me | solution 1 for D1Bound5.finiteP_monomial_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:34.767519+00:00
-- url     : https://prove2.me/submissions/b6ae807b-953c-4392-9652-6fd9f6df3542

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three















theorem _root_.solution (A B S : ℝ) (hA : 1 ≤ A)
    (hAB : A ≤ B) (hBS : B ≤ S) (i j l : ℕ)
    (hexp : (i+j+l ≤ 5 ∧ l ≤ 2) ∨ (i+j ≤ 1 ∧ l ≤ 3)) :
    A^i*B^j*S^l ≤ max (B*S^3) (B^3*S^2) := by
  have hB : 1 ≤ B := hA.trans hAB
  have hS : 1 ≤ S := hB.trans hBS
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hfirst : A^i*B^j*S^l ≤ B^(i+j)*S^l := by
    rw [pow_add]
    gcongr
  apply hfirst.trans
  rcases hexp with ⟨ht,hl⟩ | ⟨ht,hl⟩
  · apply le_trans _ (le_max_right _ _)
    by_cases hn : i+j ≤ 3
    · gcongr
    · have hsplit : i+j = 3+(i+j-3) := by omega
      have hsmall : i+j-3+l ≤ 2 := by omega
      calc
        B^(i+j)*S^l = B^3*(B^(i+j-3)*S^l) := by rw [← mul_assoc, ← pow_add, ← hsplit]
        _ ≤ B^3*(S^(i+j-3)*S^l) := by gcongr
        _ = B^3*S^(i+j-3+l) := by rw [pow_add]
        _ ≤ B^3*S^2 := by gcongr
  · apply le_trans _ (le_max_left _ _)
    calc
      B^(i+j)*S^l ≤ B^1*S^3 := by gcongr
      _ = B*S^3 := by ring













end D1Bound5
end
