-- Prove2me | solution 1 for D1Bound5.productFive_schur_near_of_coordinate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:49:08.66587+00:00
-- url     : https://prove2.me/submissions/1d6cc97e-d971-4f0c-a050-bc30dbd4b286

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
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_productFive_schur_near_of_entrywise
import Theorems.Thm_D1Bound5_productFive_schur_scalar_correction_lt

section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace D1Bound5







/-- Schur proximity from prefix and componentwise coordinate estimates. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (v w : Fin 4 → ℂ) (d : ℂ)
    (hF : ‖F - halfOffDiagonal‖ ≤ (11/96 : ℝ))
    (hd : (54 : ℝ) ≤ ‖d‖)
    (hw : ∀ i, ‖w i/d‖ < (1/18 : ℝ))
    (hv : ∀ i, ‖v i‖ < (3/4 : ℝ)) :
    ‖productFiveSchur F v w d - halfOffDiagonal‖ < (1/2 : ℝ) := by
  have hentry : ∀ i j,
      ‖(productFiveSchur F v w d - F) i j‖ < (9/100 : ℝ) := by
    intro i j
    have hh := productFive_schur_scalar_correction_lt
      (w i) (w j) (v i) (v j) d hd (hw i) (hw j) (hv i) (hv j)
    have heq : (productFiveSchur F v w d - F) i j =
        -((w i * v j + v i * w j) / d + v i * v j / d^2) := by
      simp only [Matrix.sub_apply, productFiveSchur]
      ring
    rw [heq, norm_neg]
    exact hh
  exact productFive_schur_near_of_entrywise F
    (productFiveSchur F v w d) hF hentry



end D1Bound5
end
