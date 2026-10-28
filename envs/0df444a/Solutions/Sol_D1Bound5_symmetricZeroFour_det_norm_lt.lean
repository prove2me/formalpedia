-- Prove2me | solution 1 for D1Bound5.symmetricZeroFour_det_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:28.884994+00:00
-- url     : https://prove2.me/submissions/6a5d9452-fb13-4574-9ce6-a55bcc683bbf

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
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions
import Theorems.Thm_D1Bound5_nearHalf_product_nearQuarter
import Theorems.Thm_D1Bound5_symmetricZeroFour_det
import Theorems.Thm_D1Bound5_threePairDetPolynomial_bound

section
open Matrix

namespace D1Bound5



end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5

/-- A direct four-by-four determinant bound, without singular values. -/
theorem _root_.solution
    (x y z u v w : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hu : ‖u - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hv : ‖v - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hw : ‖w - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
      Matrix (Fin 4) (Fin 4) ℂ).det‖ <
    productFourH * productFourS^3 := by
  rw [symmetricZeroFour_det]
  exact lt_trans
    (threePairDetPolynomial_bound (x*w) (y*v) (z*u)
      (nearHalf_product_nearQuarter x w hx hw)
      (nearHalf_product_nearQuarter y v hy hv)
      (nearHalf_product_nearQuarter z u hz hu))
    (by unfold productFourH productFourS; norm_num)



end D1Bound5

namespace D1Bound5





end D1Bound5
end
