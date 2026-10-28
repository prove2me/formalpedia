-- Prove2me | solution 1 for D1Bound5.mixed_triple_cofactor_radius
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:36.494948+00:00
-- url     : https://prove2.me/submissions/4035906a-7709-4ccc-8c0c-a7beb0cb4645

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

/-- A product of three independently perturbed complex half-units. -/
theorem _root_.solution (x y z : ℂ) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ a)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ b)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ c) :
    ‖2*x*y*z-(1/4 : ℂ)‖ ≤
      2*a*(1/2+b)*(1/2+c) + b*(1/2+c) + c/2 := by
  have hny : ‖y‖ ≤ 1/2+b := by
    have h := norm_add_le (y-(1/2 : ℂ)) (1/2 : ℂ)
    have heq : y-(1/2 : ℂ)+(1/2 : ℂ)=y := by ring
    rw [heq] at h
    have hhalf : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
    rw [hhalf] at h
    linarith
  have hnz : ‖z‖ ≤ 1/2+c := by
    have h := norm_add_le (z-(1/2 : ℂ)) (1/2 : ℂ)
    have heq : z-(1/2 : ℂ)+(1/2 : ℂ)=z := by ring
    rw [heq] at h
    have hhalf : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
    rw [hhalf] at h
    linarith
  have hprod : ‖x-(1/2 : ℂ)‖ * ‖y‖ * ‖z‖ ≤ a*(1/2+b)*(1/2+c) := by
    gcongr
  have hprod2 : ‖y-(1/2 : ℂ)‖ * ‖z‖ ≤ b*(1/2+c) := by
    gcongr
  have hid : 2*x*y*z-(1/4 : ℂ) =
      2*(x-1/2)*y*z + (y-1/2)*z + (z-1/2)/2 := by ring
  rw [hid]
  have htri :
      ‖2*(x-1/2)*y*z + (y-1/2)*z + (z-1/2)/2‖ ≤
      ‖2*(x-1/2)*y*z‖ + ‖(y-1/2)*z‖ + ‖(z-1/2)/2‖ := by
    have h1 := norm_add_le (2*(x-1/2)*y*z + (y-1/2)*z) ((z-1/2)/2)
    have h2 := norm_add_le (2*(x-1/2)*y*z) ((y-1/2)*z)
    linarith
  have hn1 : ‖2*(x-1/2)*y*z‖ ≤ 2*(a*(1/2+b)*(1/2+c)) := by
    have heq : ‖2*(x-1/2)*y*z‖ = 2*(‖x-1/2‖*‖y‖*‖z‖) := by
      simp [norm_mul]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hprod (by norm_num)
  have hn2 : ‖(y-1/2)*z‖ ≤ b*(1/2+c) := by
    rw [norm_mul]
    exact hprod2
  have hn3 : ‖(z-1/2)/2‖ ≤ c/2 := by
    have heq : ‖(z-1/2)/2‖ = ‖z-1/2‖/2 := by simp [norm_div]
    rw [heq]
    linarith
  linarith only [htri,hn1,hn2,hn3]





end D1Bound5


namespace D1Bound5







end D1Bound5
end
