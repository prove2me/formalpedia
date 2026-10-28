-- Prove2me | solution 1 for D1Bound5.mixedSymmetricFour_det_lt_33_128
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:54:47.711406+00:00
-- url     : https://prove2.me/submissions/46a7bb02-e4f2-4af3-8539-f7f71dfb7beb

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
import Theorems.Thm_D1Bound5_mixedThreePairDet_norm_lt_33_128
import Theorems.Thm_D1Bound5_symmetricZeroFour_det

section
open Matrix

namespace D1Bound5





/-- Sharpened mixed determinant bound for the exact symmetric matrix. -/
theorem _root_.solution (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (1/18 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (1/64 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (1/64 : ℝ)) :
    ‖( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
      Matrix (Fin 4) (Fin 4) ℂ).det‖ < (33/128 : ℝ) := by
  rw [symmetricZeroFour_det]
  exact mixedThreePairDet_norm_lt_33_128 (x*w) (y*v) (z*u)
    (mixedPairProduct_nearQuarter x w hx hw)
    (mixedPairProduct_nearQuarter y v hy hv)
    (mixedPairProduct_nearQuarter z u hz hu)



end D1Bound5
end
