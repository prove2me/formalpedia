-- Prove2me | solution 1 for D1Bound5.frontier_cubic_product_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:40.453252+00:00
-- url     : https://prove2.me/submissions/ff38da35-fdf7-483f-937e-1bab710904a3

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- A product of three near-half factors has the exact leading one-eighth
and a remainder bounded by the corresponding product of envelopes. -/
theorem _root_.solution (x y z : ℂ) (k l : ℝ)
    (hk : (1/2 : ℝ) ≤ k) (hl : (1/2 : ℝ) ≤ l)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ k-1/2)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ k-1/2)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ l-1/2) :
    ‖x*y*z‖ ≤ k^2*l ∧ ‖x*y*z-(1/8 : ℂ)‖ ≤ k^2*l-1/8 := by
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hke0 : 0 ≤ k-1/2 := sub_nonneg.mpr hk
  have hle0 : 0 ≤ l-1/2 := sub_nonneg.mpr hl
  have hnx : ‖x‖ ≤ k := by
    have h := norm_add_le (x-(1/2 : ℂ)) (1/2 : ℂ)
    norm_num at h
    linarith only [h, hx]
  have hny : ‖y‖ ≤ k := by
    have h := norm_add_le (y-(1/2 : ℂ)) (1/2 : ℂ)
    norm_num at h
    linarith only [h, hy]
  have hnz : ‖z‖ ≤ l := by
    have h := norm_add_le (z-(1/2 : ℂ)) (1/2 : ℂ)
    norm_num at h
    linarith only [h, hz]
  constructor
  · rw [norm_mul, norm_mul]
    calc
      ‖x‖*‖y‖*‖z‖ ≤ k*k*l := by gcongr
      _ = k^2*l := by ring
  · have hid : x*y*z-(1/8 : ℂ) =
        (x-1/2)*y*z+(1/2 : ℂ)*(y-1/2)*z+(1/4 : ℂ)*(z-1/2) := by ring
    rw [hid]
    calc
      _ ≤ ‖(x-1/2)*y*z+(1/2 : ℂ)*(y-1/2)*z‖+
          ‖(1/4 : ℂ)*(z-1/2)‖ := norm_add_le _ _
      _ ≤ (‖(x-1/2)*y*z‖+‖(1/2 : ℂ)*(y-1/2)*z‖)+
          ‖(1/4 : ℂ)*(z-1/2)‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = ‖x-1/2‖*‖y‖*‖z‖+(1/2 : ℝ)*‖y-1/2‖*‖z‖+
          (1/4 : ℝ)*‖z-1/2‖ := by norm_num [norm_mul]
      _ ≤ (k-1/2)*k*l+(1/2 : ℝ)*(k-1/2)*l+(1/4 : ℝ)*(l-1/2) := by
        gcongr
      _ = k^2*l-1/8 := by ring





end D1Bound5
end
