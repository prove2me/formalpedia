-- Prove2me | solution 1 for D1Bound5.QuadInt.hasSquareRoot_iff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:49.165787+00:00
-- url     : https://prove2.me/submissions/86ba4d8e-acfc-4cef-bce5-77d9af0b0f4a

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_rootCandidate_complete

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}









/-- A returned root is an actual root without any discriminant hypothesis. -/
theorem squareRoot_sound {z r : QuadInt tau nu} (h : squareRoot z = some r) : r*r = z := by
  change (if rootCandidate z*rootCandidate z = z then some (rootCandidate z) else none) = some r at h
  split_ifs at h with hc
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact hc



/-- A square always yields a returned root. -/
theorem squareRoot_complete (hd : 0 < discriminant tau nu)
    {z : QuadInt tau nu} (hz : ∃ r, r*r = z) :
    squareRoot z = some (rootCandidate z) := by
  simp only [squareRoot, rootCandidate_complete hd hz, if_true]



/-- The checker is necessary and sufficient, not merely a source of
positive witnesses or a one-sided modular obstruction. -/
theorem _root_.solution (hd : 0 < discriminant tau nu) (z : QuadInt tau nu) :
    hasSquareRoot z = true ↔ ∃ r : QuadInt tau nu, r*r = z := by
  cases h : squareRoot z with
  | none =>
    simp only [hasSquareRoot, h, Option.isSome_none, Bool.false_eq_true, false_iff]
    intro hz
    have hc := squareRoot_complete hd hz
    rw [h] at hc
    contradiction
  | some r =>
    simp only [hasSquareRoot, h, Option.isSome_some, true_iff]
    exact ⟨r, squareRoot_sound h⟩







end D1Bound5.QuadInt
end
