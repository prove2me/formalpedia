-- Prove2me | solution 1 for D1Bound5.five_compatible_bilinear_p_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:42:27.224248+00:00
-- url     : https://prove2.me/submissions/f1d1e35f-8483-43b6-8e40-ecdf8d9268e0

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Theorems.Thm_D1Bound5_fiveLastColumn_l2_bounds
import Theorems.Thm_D1Bound5_fiveSignedEntryGood_last_column
import Theorems.Thm_D1Bound5_five_compatible_inverse_vector_bound
import Theorems.Thm_D1Bound5_productFive_selfBilinear_norm_lt_one

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





end D1Bound5

open scoped InnerProductSpace

namespace D1Bound5





/-- A single five-entry original-ring sign choice supplies the p-bound
needed by the rank-two Schur determinant argument. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (S : Matrix (Fin 5) (Fin 5) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hgood : ∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j)) :
    let E := normalizedRootError (fun i => f (a i)) u (fun i j => f (S i j))
    let F := fivePrefixError E
    let v := fiveLastError E
    ‖v ⬝ᵥ (F⁻¹ *ᵥ v)‖ < (1 : ℝ) := by
  let E := normalizedRootError (fun i => f (a i)) u (fun i j => f (S i j))
  let F := fivePrefixError E
  let v := fiveLastError E
  have hlast := fiveSignedEntryGood_last_column f a u S hgood
  have hv := (fiveLastColumn_l2_bounds v (fun i => (hlast i).2)).2
  have hInv := five_compatible_inverse_vector_bound f a u S hu hdiag hgood
  exact productFive_selfBilinear_norm_lt_one F v hv hInv

end D1Bound5
end
