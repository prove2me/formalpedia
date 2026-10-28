-- Prove2me | solution 1 for D1Bound5.symmetricZeroFour_det
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:04.782993+00:00
-- url     : https://prove2.me/submissions/07922667-c25e-46b1-b219-1cca0c84c8ed

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

section
open Matrix

namespace D1Bound5

/-- Exact determinant polynomial of a symmetric zero-diagonal four-by-four matrix. -/
theorem _root_.solution (x y z u v w : ℂ) :
    ( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
      Matrix (Fin 4) (Fin 4) ℂ).det =
    (x*w)^2 + (y*v)^2 + (z*u)^2 -
      2 * ((x*w)*(y*v) + (x*w)*(z*u) + (y*v)*(z*u)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  simp (config := {decide := true}) [Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.of_apply, Fin.succAbove]
  ring

end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5





end D1Bound5
end
