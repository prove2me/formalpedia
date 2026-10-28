-- Prove2me | solution 1 for D1Bound5.mixedSymmetricFour_det_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:18.114833+00:00
-- url     : https://prove2.me/submissions/c60e4f91-ef67-471b-b412-167b381dfa5e

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
import Theorems.Thm_D1Bound5_mixedPairProduct_nearQuarter
import Theorems.Thm_D1Bound5_mixedThreePairDet_norm_lt
import Theorems.Thm_D1Bound5_symmetricZeroFour_det

section
open Matrix

namespace D1Bound5





/-- A symmetric mixed normalized matrix satisfies a uniform determinant
bound, with no singular-value or invertibility assumptions. -/
theorem _root_.solution (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
      Matrix (Fin 4) (Fin 4) ℂ).det‖ < (3/10 : ℝ) := by
  rw [symmetricZeroFour_det]
  exact mixedThreePairDet_norm_lt (x*w) (y*v) (z*u)
    (mixedPairProduct_nearQuarter x w hx hw)
    (mixedPairProduct_nearQuarter y v hy hv)
    (mixedPairProduct_nearQuarter z u hz hu)

end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5



end D1Bound5
end
