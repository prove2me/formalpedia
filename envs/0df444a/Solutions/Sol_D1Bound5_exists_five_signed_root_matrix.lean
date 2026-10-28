-- Prove2me | solution 1 for D1Bound5.exists_five_signed_root_matrix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:15.54277+00:00
-- url     : https://prove2.me/submissions/47f2d9a1-7c56-433b-878b-7ae76cba600f

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
import Theorems.Thm_D1Bound5_fiveSignedEntryGood_or_neg
import Theorems.Thm_D1Bound5_fiveSignedEntryGood_swap

section
namespace D1Bound5









/-- One simultaneous choice for all ten original-ring roots. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (M : Matrix (Fin 5) (Fin 5) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (_hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hfirst : ∀ i j, i ≠ j →
      3 ≤ ‖f (a i) * f (a j)‖)
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      9 ≤ ‖f (a i) * f (a j)‖)
    (hlast : ∀ i j, i ≠ j → i = 4 ∨ j = 4 →
      54 ≤ ‖f (a i) * f (a j)‖) :
    ∃ S : Matrix (Fin 5) (Fin 5) R,
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → S i j = M i j ∨ S i j = -M i j) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i * a j + 1) ∧
      (∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j)) := by
  classical
  let q : Fin 5 → Fin 5 → R := fun i j =>
    if FiveSignedEntryGood f a u i j (M i j) then
      M i j else -M i j
  have hqsign (i j : Fin 5) : q i j = M i j ∨ q i j = -M i j := by
    dsimp [q]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hqgood (i j : Fin 5) (hij : i ≠ j) :
      FiveSignedEntryGood f a u i j (q i j) := by
    dsimp [q]
    split_ifs with h
    · exact h
    · rcases fiveSignedEntryGood_or_neg f a u i j (M i j) hu
        (hroot i j hij) (hfirst i j hij) (hlater i j hij) (hlast i j hij) with hp | hn
      · exact False.elim (h hp)
      · exact hn
  let S : Matrix (Fin 5) (Fin 5) R := fun i j =>
    if i = j then a i else q (min i j) (max i j)
  have hSdiag (i : Fin 5) : S i i = a i := by simp [S]
  have hSsym (i j : Fin 5) : S i j = S j i := by
    by_cases h : i = j
    · subst j
      rfl
    · simp [S, h, Ne.symm h, min_comm, max_comm]
  have hSsign (i j : Fin 5) (hij : i ≠ j) :
      S i j = M i j ∨ S i j = -M i j := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · simpa [S, hij, min_eq_left hlt.le, max_eq_right hlt.le] using hqsign i j
    · exact False.elim (hij heq)
    · have hq := hqsign j i
      simpa [S, hij, min_eq_right hgt.le, max_eq_left hgt.le, hsymm j i] using hq
  have hSroot (i j : Fin 5) (hij : i ≠ j) :
      (S i j)^2 = a i * a j + 1 := by
    rcases hSsign i j hij with h | h
    · rw [h]
      exact hroot i j hij
    · rw [h]
      simpa only [neg_sq] using hroot i j hij
  have hSgood (i j : Fin 5) (hij : i ≠ j) :
      FiveSignedEntryGood f a u i j (S i j) := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · simpa [S, hij, min_eq_left hlt.le, max_eq_right hlt.le] using
        hqgood i j hij
    · exact False.elim (hij heq)
    · have h := fiveSignedEntryGood_swap f a u j i (q j i)
        (hqgood j i hij.symm)
      simpa [S, hij, min_eq_right hgt.le, max_eq_left hgt.le] using h
  exact ⟨S, hSdiag, hSsym, hSsign, hSroot, hSgood⟩







open scoped NumberField
open Module








end D1Bound5
end
