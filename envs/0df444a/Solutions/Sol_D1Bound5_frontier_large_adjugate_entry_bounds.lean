-- Prove2me | solution 1 for D1Bound5.frontier_large_adjugate_entry_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:38:16.972052+00:00
-- url     : https://prove2.me/submissions/5247f27d-daef-4176-a8b0-08070bf65419

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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_nearHalf_offDiagonal_cofactor_bound
import Theorems.Thm_D1Bound5_nearHalf_triple_cofactor_bound
import Theorems.Thm_D1Bound5_symmetricFour_adjugate_formula

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5

private theorem frontier_norm_of_near (x c : ℂ) (e : ℝ)
    (h : ‖x-c‖ < e) : ‖x‖ < ‖c‖+e := by
  have hid : x = (x-c)+c := by ring
  calc
    ‖x‖ = ‖(x-c)+c‖ := congrArg norm hid
    _ ≤ ‖x-c‖+‖c‖ := norm_add_le _ _
    _ < ‖c‖+e := by linarith only [h]

private theorem frontier_diagonal_cofactor (x y z : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖2*x*y*z‖ ≤ (273/1000 : ℝ) := by
  have h := frontier_norm_of_near (2*x*y*z) (1/4) (23/1000)
    (nearHalf_triple_cofactor_bound x y z hx hy hz)
  norm_num at h
  simpa [norm_mul] using h.le

private theorem frontier_offDiagonal_cofactor (x y z u v w : ℂ)
    (hx : ‖x-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hz : ‖z-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hu : ‖u-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hv : ‖v-(1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hw : ‖w-(1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖w^2*x-w*z*u-w*y*v‖ ≤ (1447/10000 : ℝ) := by
  have hnear := nearHalf_offDiagonal_cofactor_bound x y z u v w hx hy hz hu hv hw
  have h := frontier_norm_of_near (w^2*x-w*z*u-w*y*v) (-(1/8)) (197/10000)
    (by simpa only [sub_neg_eq_add] using hnear)
  norm_num at h
  exact h.le

/-- Keep diagonal and off-diagonal cofactor bounds separately. This is
sharper for the already very unequal tuple coordinates than replacing the
adjugate by its operator norm. All estimates are proved dependencies. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hzero : ∀ i, F i i = 0) (hsym : ∀ i j, F i j = F j i)
    (hnear : ∀ i j, i ≠ j → ‖F i j-(1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ∀ i j, ‖F.adjugate i j‖ ≤
      if i = j then (273/1000 : ℝ) else (1447/10000 : ℝ) := by
  let x := F 0 1
  let y := F 0 2
  let z := F 0 3
  let u := F 1 2
  let v := F 1 3
  let w := F 2 3
  have hrepr : F = !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp (config := {decide := true}) [x,y,z,u,v,w,hzero] <;>
        (first | exact hsym _ _ | exact (hsym _ _).symm))
  have hAdj : F.adjugate =
      !![2*u*v*w, w^2*x-w*z*u-w*y*v, v^2*y-v*z*u-v*x*w, u^2*z-u*y*v-u*x*w;
         w^2*x-w*z*u-w*y*v, 2*y*z*w, z^2*u-z*y*v-z*x*w, y^2*v-y*x*w-y*z*u;
         v^2*y-v*z*u-v*x*w, z^2*u-z*y*v-z*x*w, 2*x*z*v, x^2*w-x*y*v-x*z*u;
         u^2*z-u*y*v-u*x*w, y^2*v-y*x*w-y*z*u, x^2*w-x*y*v-x*z*u, 2*x*y*u] := by
    rw [hrepr]
    exact symmetricFour_adjugate_formula x y z u v w
  have hx := hnear 0 1 (by decide)
  have hy := hnear 0 2 (by decide)
  have hz := hnear 0 3 (by decide)
  have hu := hnear 1 2 (by decide)
  have hv := hnear 1 3 (by decide)
  have hw := hnear 2 3 (by decide)
  have h00 := frontier_diagonal_cofactor u v w hu hv hw
  have h11 := frontier_diagonal_cofactor y z w hy hz hw
  have h22 := frontier_diagonal_cofactor x z v hx hz hv
  have h33 := frontier_diagonal_cofactor x y u hx hy hu
  have h01 := frontier_offDiagonal_cofactor x y z u v w hx hy hz hu hv hw
  have h02 := frontier_offDiagonal_cofactor y x z u w v hy hx hz hu hw hv
  have h03 := frontier_offDiagonal_cofactor z x y v w u hz hx hy hv hw hu
  have h12 := frontier_offDiagonal_cofactor u x y v w z hu hx hy hv hw hz
  have h13 := frontier_offDiagonal_cofactor v z x w u y hv hz hx hw hu hy
  have h23 := frontier_offDiagonal_cofactor w z y v u x hw hz hy hv hu hx
  intro i j
  rw [hAdj]
  fin_cases i <;> fin_cases j
  all_goals first
    | simpa using h00
    | simpa using h11
    | simpa using h22
    | simpa using h33
    | simpa using h01
    | simpa using h02
    | simpa using h03
    | simpa using h12
    | simpa using h13
    | simpa using h23

end D1Bound5
end
