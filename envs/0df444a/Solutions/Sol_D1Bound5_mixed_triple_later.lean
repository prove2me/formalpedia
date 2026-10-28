-- Prove2me | solution 1 for D1Bound5.mixed_triple_later
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:29.791611+00:00
-- url     : https://prove2.me/submissions/ad59c6b6-1b2b-4228-b99d-881193381a32

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
import Theorems.Thm_D1Bound5_mixed_triple_cofactor_radius

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5



/-- Later-block diagonal cofactor: three small radius perturbations. -/
theorem _root_.solution (x y z : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖2*x*y*z-(1/4 : ℂ)‖ < (1/40 : ℝ) := by
  have h := mixed_triple_cofactor_radius x y z (1/64) (1/64) (1/64)
    (by norm_num) (by norm_num) (by norm_num) hx.le hy.le hz.le
  have hn : 2*(1/64 : ℝ)*(1/2+1/64)*(1/2+1/64) +
      (1/64)*(1/2+1/64)+(1/64)/2 < 1/40 := by norm_num
  exact lt_of_le_of_lt h hn



end D1Bound5


namespace D1Bound5







end D1Bound5
end
