-- Prove2me | solution 1 for D1Bound5.productFive_schur_near_of_entrywise
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:16.43293+00:00
-- url     : https://prove2.me/submissions/671172b9-44cd-4825-ae48-e0b40a6ffbcc

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
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_four_all_entries_operator_norm_lt

section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace D1Bound5



/-- A determinant-free proximity criterion for a four-by-four Schur matrix. -/
theorem _root_.solution
    (F G : Matrix (Fin 4) (Fin 4) ℂ)
    (hF : ‖F - halfOffDiagonal‖ ≤ (11/96 : ℝ))
    (hG : ∀ i j, ‖(G - F) i j‖ < (9/100 : ℝ)) :
    ‖G - halfOffDiagonal‖ < (1/2 : ℝ) := by
  have hpert : ‖G - F‖ < (4 : ℝ) * (9/100 : ℝ) :=
    four_all_entries_operator_norm_lt (G-F) (9/100) (by norm_num) hG
  have hdecomp : G - halfOffDiagonal =
      (G - F) + (F - halfOffDiagonal) := by abel
  calc
    ‖G - halfOffDiagonal‖ =
        ‖(G - F) + (F - halfOffDiagonal)‖ := congrArg norm hdecomp
    _ ≤ ‖G-F‖ + ‖F-halfOffDiagonal‖ := norm_add_le _ _
    _ < (4 : ℝ)*(9/100) + (11/96) := by linarith only [hpert,hF]
    _ < 1/2 := by norm_num







end D1Bound5
end
