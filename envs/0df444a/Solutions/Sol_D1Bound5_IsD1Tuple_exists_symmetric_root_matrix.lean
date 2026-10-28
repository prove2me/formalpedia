-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.exists_symmetric_root_matrix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:12:25.80267+00:00
-- url     : https://prove2.me/submissions/e53ea48f-6b43-4cbe-a755-2282f5eae957

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_TupleRootMatrixBridge_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5





private theorem tuplePairRoot_sq {R : Type*} [CommRing R] {n : ℕ}
    (t : Fin n → R) (ht : IsD1Tuple t) (i j : Fin n) (hij : i ≠ j) :
    (tuplePairRoot t ht i j hij)^2 = t i * t j + 1 := by
  have hr : (tuplePairRoot t ht i j hij)^2 =
      t (min i j) * t (max i j) + 1 := by
    unfold tuplePairRoot
    simpa only [pow_two] using
      (Classical.choose_spec
        (ht.2.2 (min i j) (max i j) (min_ne_max_fin i j hij)))
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hr
  · simpa [min_eq_right hgt.le, max_eq_left hgt.le, mul_comm] using hr

private theorem tuplePairRoot_symm {R : Type*} [CommRing R] {n : ℕ}
    (t : Fin n → R) (ht : IsD1Tuple t) (i j : Fin n) (hij : i ≠ j) :
    tuplePairRoot t ht i j hij = tuplePairRoot t ht j i (Ne.symm hij) := by
  simp [tuplePairRoot, min_comm, max_comm]

/-- Every indexed D(1)-tuple admits a symmetric root matrix over the same
original commutative ring. The diagonal is the tuple itself. -/
theorem _root_.solution {R : Type*} [CommRing R]
    {n : ℕ} (t : Fin n → R) (ht : IsD1Tuple t) :
    ∃ M : Matrix (Fin n) (Fin n) R,
      (∀ i, M i i = t i) ∧
      (∀ i j, M i j = M j i) ∧
      (∀ i j, i ≠ j → (M i j)^2 = t i * t j + 1) := by
  classical
  let M : Matrix (Fin n) (Fin n) R :=
    fun i j => if hij : i = j then t i else tuplePairRoot t ht i j hij
  refine ⟨M, ?_, ?_, ?_⟩
  · intro i
    simp [M]
  · intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hji : j ≠ i := Ne.symm hij
      simp only [M, dif_neg hij, dif_neg hji]
      exact tuplePairRoot_symm t ht i j hij
  · intro i j hij
    simpa only [M, dif_neg hij] using tuplePairRoot_sq t ht i j hij



end D1Bound5
end
