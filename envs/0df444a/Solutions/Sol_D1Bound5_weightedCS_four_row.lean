-- Prove2me | solution 1 for D1Bound5.weightedCS_four_row
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:23.501303+00:00
-- url     : https://prove2.me/submissions/56e725b8-383c-4797-87da-441f8fa39d18

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

/-- Weighted finite Cauchy--Schwarz without square roots or positivity of x. -/
theorem _root_.solution (b w x : Fin 4 → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hw : ∀ j, 0 < w j) :
    (∑ j, b j * x j)^2 ≤
      (∑ j, b j * w j) * (∑ j, b j * (x j)^2 / w j) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro j _
    exact mul_nonneg (hb j) (hw j).le
  · intro j _
    exact div_nonneg (mul_nonneg (hb j) (sq_nonneg _)) (hw j).le
  · intro j _
    have hj : w j ≠ 0 := ne_of_gt (hw j)
    apply le_of_eq
    field_simp

end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5





end D1Bound5
end
