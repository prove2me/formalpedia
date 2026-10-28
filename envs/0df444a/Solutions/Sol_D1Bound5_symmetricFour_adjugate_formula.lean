-- Prove2me | solution 1 for D1Bound5.symmetricFour_adjugate_formula
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:54.129982+00:00
-- url     : https://prove2.me/submissions/e3fb42f9-0f53-4db9-8875-16727739e7f9

import Lean.Util.CollectAxioms
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_AdjugateCoverage_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





/-- All sixteen cofactors of the symmetric zero-diagonal four-by-four matrix. -/
theorem _root_.solution (x y z u v w : ℂ) :
    (symmetricFour x y z u v w).adjugate = symmetricFourAdj x y z u v w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.adjugate_apply, Matrix.det_succ_row_zero]
     simp (config := {decide := true})
       [symmetricFour, symmetricFourAdj, Matrix.updateRow_apply,
        Pi.single_apply, Fin.sum_univ_succ, Matrix.det_fin_three,
        Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove] <;> ring)





end D1Bound5
end
