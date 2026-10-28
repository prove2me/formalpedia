-- Prove2me | solution 1 for D1Bound5.mixed_offDiagonal_later
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:18.929953+00:00
-- url     : https://prove2.me/submissions/ffdae45b-3d43-4383-9d2e-ff804396d68b

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
import Theorems.Thm_D1Bound5_mixed_offDiagonal_cofactor_radius

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







end D1Bound5


namespace D1Bound5





/-- Off-diagonal cofactor for distinct positive row/column indices. -/
theorem _root_.solution (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖z^2*u-z*y*v-z*x*w+(1/8 : ℂ)‖ < (47/1000 : ℝ) := by
  have h := mixed_offDiagonal_cofactor_radius u x y v w z
    (1/64) (1/18) (1/18) (1/64) (1/64) (1/18)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hu.le hx.le hy.le hv.le hw.le hz.le
  have hn :
      ((1/64+1/18+1/64+1/18+1/64)/4 +
      (1/18)*(1/64+(1/18+1/64+1/18+1/64)/2) +
      ((1/18)^2+(1/18)*(1/64)+(1/18)*(1/64))/2 +
      (1/18)*((1/64)*(1/18)+(1/18)*(1/64)+(1/18)*(1/64)) : ℝ) <
      47/1000 := by norm_num
  exact lt_of_le_of_lt h hn

end D1Bound5
end
