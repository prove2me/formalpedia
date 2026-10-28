-- Prove2me | solution 1 for D1Bound5.frontier_three_envelope_product
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:22:33.511873+00:00
-- url     : https://prove2.me/submissions/a9aa8d6b-dd14-4bdc-96f7-b76af0c0084b

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
open Matrix

namespace D1Bound5

theorem _root_.solution (x y z : ℂ) (a b c : ℝ)
    (ha : 1/2 ≤ a) (hb : 1/2 ≤ b) (hc : 1/2 ≤ c)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ a-1/2)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ b-1/2)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ c-1/2) :
    ‖x*y*z‖ ≤ a*b*c ∧ ‖x*y*z-(1/8 : ℂ)‖ ≤ a*b*c-1/8 := by
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hc0 : 0 ≤ c := by linarith only [hc]
  have hnx : ‖x‖ ≤ a := by
    have hh := norm_add_le (x-(1/2 : ℂ)) (1/2 : ℂ)
    norm_num at hh
    linarith only [hh,hx]
  have hny : ‖y‖ ≤ b := by
    have hh := norm_add_le (y-(1/2 : ℂ)) (1/2 : ℂ)
    norm_num at hh
    linarith only [hh,hy]
  have hnz : ‖z‖ ≤ c := by
    have hh := norm_add_le (z-(1/2 : ℂ)) (1/2 : ℂ)
    norm_num at hh
    linarith only [hh,hz]
  constructor
  · simp only [norm_mul]
    gcongr
  · have hid : x*y*z-(1/8 : ℂ) =
        (x-1/2)*y*z+(1/2 : ℂ)*(y-1/2)*z+(1/4 : ℂ)*(z-1/2) := by ring
    rw [hid]
    calc
      _ ≤ ‖(x-1/2)*y*z+(1/2 : ℂ)*(y-1/2)*z‖+‖(1/4 : ℂ)*(z-1/2)‖ := norm_add_le _ _
      _ ≤ ‖(x-1/2)*y*z‖+‖(1/2 : ℂ)*(y-1/2)*z‖+‖(1/4 : ℂ)*(z-1/2)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = ‖x-1/2‖*‖y‖*‖z‖+(1/2 : ℝ)*‖y-1/2‖*‖z‖+(1/4 : ℝ)*‖z-1/2‖ := by
        norm_num [norm_mul]
      _ ≤ (a-1/2)*b*c+(1/2 : ℝ)*(b-1/2)*c+(1/4 : ℝ)*(c-1/2) := by gcongr
      _ = a*b*c-1/8 := by ring







end D1Bound5
end
