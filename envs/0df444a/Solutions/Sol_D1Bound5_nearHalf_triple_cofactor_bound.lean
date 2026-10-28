-- Prove2me | solution 1 for D1Bound5.nearHalf_triple_cofactor_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:48.792129+00:00
-- url     : https://prove2.me/submissions/21bd4dfc-c3a9-45bc-a578-ed333dc2f846

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

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







end D1Bound5


namespace D1Bound5





end D1Bound5

namespace D1Bound5

/-- Uniform diagonal cofactor error for three entries near one half. -/
theorem _root_.solution (x y z : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖2*x*y*z - (1/4 : ℂ)‖ < (23/1000 : ℝ) := by
  let e : ℝ := 128/8649
  let t : ℝ := 1/2 + e
  have hxe : ‖x - (1/2 : ℂ)‖ ≤ e := hx.le
  have hye : ‖y - (1/2 : ℂ)‖ ≤ e := hy.le
  have hze : ‖z - (1/2 : ℂ)‖ ≤ e := hz.le
  have hny : ‖y‖ ≤ t := by
    have hn := norm_add_le (y-(1/2 : ℂ)) (1/2 : ℂ)
    have heq : y-(1/2 : ℂ)+(1/2 : ℂ)=y := by ring
    rw [heq] at hn
    have hn2 : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
    rw [hn2] at hn
    dsimp [t]
    linarith only [hn, hye]
  have hnz : ‖z‖ ≤ t := by
    have hn := norm_add_le (z-(1/2 : ℂ)) (1/2 : ℂ)
    have heq : z-(1/2 : ℂ)+(1/2 : ℂ)=z := by ring
    rw [heq] at hn
    have hn2 : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
    rw [hn2] at hn
    dsimp [t]
    linarith only [hn, hze]
  have hp : ‖x-(1/2 : ℂ)‖*‖y‖*‖z‖ ≤ e*t*t := by
    have h1 : ‖x-(1/2 : ℂ)‖*‖y‖ ≤ e*‖y‖ :=
      mul_le_mul_of_nonneg_right hxe (norm_nonneg _)
    have h2 : e*‖y‖ ≤ e*t :=
      mul_le_mul_of_nonneg_left hny (by norm_num [e])
    have h3 : (‖x-(1/2 : ℂ)‖*‖y‖)*‖z‖ ≤ (e*t)*‖z‖ :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) (norm_nonneg _)
    have h4 : (e*t)*‖z‖ ≤ (e*t)*t :=
      mul_le_mul_of_nonneg_left hnz (by norm_num [e,t])
    exact le_trans h3 h4
  have hq : ‖y-(1/2 : ℂ)‖*‖z‖ ≤ e*t := by
    have h1 := mul_le_mul_of_nonneg_right hye (norm_nonneg z)
    have h2 : e*‖z‖ ≤ e*t :=
      mul_le_mul_of_nonneg_left hnz (by norm_num [e])
    exact le_trans h1 h2
  have hid : 2*x*y*z - (1/4 : ℂ) =
      2*(x-1/2)*y*z + (y-1/2)*z + (z-1/2)/2 := by ring
  rw [hid]
  have htri :
      ‖2*(x-1/2)*y*z + (y-1/2)*z + (z-1/2)/2‖ ≤
      ‖2*(x-1/2)*y*z‖ + ‖(y-1/2)*z‖ + ‖(z-1/2)/2‖ := by
    have h1 := norm_add_le (2*(x-1/2)*y*z + (y-1/2)*z) ((z-1/2)/2)
    have h2 := norm_add_le (2*(x-1/2)*y*z) ((y-1/2)*z)
    linarith only [h1,h2]
  have hn1 : ‖2*(x-1/2)*y*z‖ ≤ 2*(e*t*t) := by
    have heq : ‖2*(x-1/2)*y*z‖ = 2*(‖x-1/2‖*‖y‖*‖z‖) := by
      simp [norm_mul]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hp (by norm_num)
  have hn2 : ‖(y-1/2)*z‖ ≤ e*t := by
    rw [norm_mul]
    exact hq
  have hn3 : ‖(z-1/2)/2‖ ≤ e/2 := by
    have heq : ‖(z-1/2)/2‖ = ‖z-1/2‖/2 := by
      simp [norm_div]
    rw [heq]
    linarith only [hze]
  have hn : (2*(e*t*t) + e*t + e/2 : ℝ) < 23/1000 := by
    dsimp [e,t]
    norm_num
  linarith only [htri, hn1, hn2, hn3, hn]

end D1Bound5
end
