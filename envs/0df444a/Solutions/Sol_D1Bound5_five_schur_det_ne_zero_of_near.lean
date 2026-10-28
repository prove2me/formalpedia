-- Prove2me | solution 1 for D1Bound5.five_schur_det_ne_zero_of_near
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:40:40.614505+00:00
-- url     : https://prove2.me/submissions/f22c2e53-b755-463d-9b52-a5dd0b8c83dd

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
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm
import Theorems.Thm_D1Bound5_reference_perturbed_det_ne_zero

section
open scoped NumberField BigOperators Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5





/-- A one-half operator-norm neighborhood of the reference matrix is
nonsingular. This supplies the needed nonvanishing in product-five. -/
theorem _root_.solution
    (G : Matrix (Fin 4) (Fin 4) ℂ)
    (hnear : ‖G - halfOffDiagonal‖ < (1/2 : ℝ)) :
    G.det ≠ 0 := by
  apply reference_perturbed_det_ne_zero
  calc
    ‖halfOffDiagonalInverse * (G - halfOffDiagonal)‖
        ≤ ‖halfOffDiagonalInverse‖ * ‖G - halfOffDiagonal‖ :=
          Matrix.l2_opNorm_mul _ _
    _ = 2 * ‖G - halfOffDiagonal‖ := by rw [halfOffDiagonalInverse_norm]
    _ < 2 * (1/2 : ℝ) :=
      mul_lt_mul_of_pos_left hnear (by norm_num)
    _ = 1 := by norm_num





end D1Bound5
end
