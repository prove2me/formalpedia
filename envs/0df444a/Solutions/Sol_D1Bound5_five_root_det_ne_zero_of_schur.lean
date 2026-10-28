-- Prove2me | solution 1 for D1Bound5.five_root_det_ne_zero_of_schur
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:54:45.95499+00:00
-- url     : https://prove2.me/submissions/5de93a85-47e3-4900-bbda-46d9d6c1f8be

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_ProductFiveArithmeticClosure_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions
import Theorems.Thm_D1Bound5_five_normalized_root_det

section
open scoped NumberField BigOperators Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5



/-- Nonvanishing of the Schur determinant forces the original symmetric
five-entry root matrix to have nonzero determinant. No assumption on any
individual root or on the leading four-by-four determinant is needed. -/
theorem _root_.solution
    (t u : Fin 5 → ℂ) (M : Matrix (Fin 5) (Fin 5) ℂ)
    (hu : ∀ i, (u i)^2 = t i)
    (hdiag : ∀ i, M i i = t i)
    (hsym : Mᵀ = M)
    (hd : fiveLastValue t ≠ 0)
    (hG : (fiveNormalizedSchur t u M).det ≠ 0) :
    M.det ≠ 0 := by
  have hid := five_normalized_root_det t u M hu hdiag hsym hd
  change (∏ i, t i) * M.det =
    (fiveLastValue t)^2 * (fiveNormalizedSchur t u M).det at hid
  have hnonzero : (∏ i, t i) * M.det ≠ 0 := by
    rw [hid]
    exact mul_ne_zero (pow_ne_zero 2 hd) hG
  exact (mul_ne_zero_iff.mp hnonzero).2







end D1Bound5
end
