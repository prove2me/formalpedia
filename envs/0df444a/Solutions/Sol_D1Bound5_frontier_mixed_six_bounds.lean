-- Prove2me | solution 1 for D1Bound5.frontier_mixed_six_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:52:02.344063+00:00
-- url     : https://prove2.me/submissions/67fb5d4b-b985-4194-a414-2440f12421b3

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
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_frontier_cubic_product_bounds
import Theorems.Thm_D1Bound5_frontier_quartic_polynomial
import Theorems.Thm_D1Bound5_frontier_three_cubic_cofactor
import Theorems.Thm_D1Bound5_symmetricFour_adjugate_formula
import Theorems.Thm_D1Bound5_symmetricZeroFour_det

section
open Matrix

namespace D1Bound5

/-- Exact mixed-envelope bounds for the normalized four-by-four matrix.
Every cubic cofactor term has at least one later edge and at most two
first-row edges, so K=k^2*l bounds all cubic products. -/
theorem _root_.solution (x y z u v w : ℂ) (k l : ℝ)
    (hl : (1/2 : ℝ) ≤ l) (hlk : l ≤ k)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ k-1/2)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ k-1/2)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ k-1/2)
    (hu : ‖u-(1/2 : ℂ)‖ ≤ l-1/2)
    (hv : ‖v-(1/2 : ℂ)‖ ≤ l-1/2)
    (hw : ‖w-(1/2 : ℂ)‖ ≤ l-1/2) :
    let F : Matrix (Fin 4) (Fin 4) ℂ := !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0]
    ‖F.det‖ ≤ 9*k^2*l^2 ∧
    ∀ i j, ‖F.adjugate i j‖ ≤ if i = j then 2*(k^2*l) else 3*(k^2*l)-1/4 := by
  let F : Matrix (Fin 4) (Fin 4) ℂ := !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0]
  change ‖F.det‖ ≤ _ ∧ ∀ i j, ‖F.adjugate i j‖ ≤ _
  have hk : (1/2 : ℝ) ≤ k := hl.trans hlk
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hu' : ‖u-(1/2 : ℂ)‖ ≤ k-1/2 := by linarith only [hu, hlk]
  have hv' : ‖v-(1/2 : ℂ)‖ ≤ k-1/2 := by linarith only [hv, hlk]
  have hw' : ‖w-(1/2 : ℂ)‖ ≤ k-1/2 := by linarith only [hw, hlk]
  have pairBound (a b : ℂ) (ha : ‖a-(1/2 : ℂ)‖ ≤ k-1/2)
      (hb : ‖b-(1/2 : ℂ)‖ ≤ l-1/2) : ‖a*b‖ ≤ k*l := by
    have ha0 : ‖a‖ ≤ k := by
      have h := norm_add_le (a-(1/2 : ℂ)) (1/2 : ℂ)
      norm_num at h
      linarith only [h,ha]
    have hb0 : ‖b‖ ≤ l := by
      have h := norm_add_le (b-(1/2 : ℂ)) (1/2 : ℂ)
      norm_num at h
      linarith only [h,hb]
    rw [norm_mul]
    exact mul_le_mul ha0 hb0 (norm_nonneg _) hk0
  constructor
  · rw [show F = !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] from rfl,
      symmetricZeroFour_det]
    have h := frontier_quartic_polynomial (x*w) (y*v) (z*u) (k*l)
      (mul_nonneg hk0 hl0) (pairBound x w hx hw) (pairBound y v hy hv) (pairBound z u hz hu)
    convert h using 1 <;> ring
  · have hAdj : F.adjugate =
      !![2*u*v*w, w^2*x-w*z*u-w*y*v, v^2*y-v*z*u-v*x*w, u^2*z-u*y*v-u*x*w;
         w^2*x-w*z*u-w*y*v, 2*y*z*w, z^2*u-z*y*v-z*x*w, y^2*v-y*x*w-y*z*u;
         v^2*y-v*z*u-v*x*w, z^2*u-z*y*v-z*x*w, 2*x*z*v, x^2*w-x*y*v-x*z*u;
         u^2*z-u*y*v-u*x*w, y^2*v-y*x*w-y*z*u, x^2*w-x*y*v-x*z*u, 2*x*y*u] :=
      symmetricFour_adjugate_formula x y z u v w
    have h00 : ‖2*u*v*w‖ ≤ 2*(k^2*l) := by
      have h := (frontier_cubic_product_bounds v w u k l hk hl hv' hw' hu).1
      have heq : ‖2*u*v*w‖ = 2*‖u*v*w‖ := by simp [norm_mul]; ring
      rw [heq]
      have h' : ‖u*v*w‖ ≤ k^2*l := by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h
      linarith only [h']
    have h11 : ‖2*y*z*w‖ ≤ 2*(k^2*l) := by
      have h := (frontier_cubic_product_bounds y z w k l hk hl hy hz hw).1
      have heq : ‖2*y*z*w‖ = 2*‖y*z*w‖ := by simp [norm_mul]; ring
      rw [heq]
      have h' : ‖y*z*w‖ ≤ k^2*l := by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h
      linarith only [h']
    have h22 : ‖2*x*z*v‖ ≤ 2*(k^2*l) := by
      have h := (frontier_cubic_product_bounds x z v k l hk hl hx hz hv).1
      have heq : ‖2*x*z*v‖ = 2*‖x*z*v‖ := by simp [norm_mul]; ring
      rw [heq]
      have h' : ‖x*z*v‖ ≤ k^2*l := by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h
      linarith only [h']
    have h33 : ‖2*x*y*u‖ ≤ 2*(k^2*l) := by
      have h := (frontier_cubic_product_bounds x y u k l hk hl hx hy hu).1
      have heq : ‖2*x*y*u‖ = 2*‖x*y*u‖ := by simp [norm_mul]; ring
      rw [heq]
      have h' : ‖x*y*u‖ ≤ k^2*l := by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h
      linarith only [h']
    have h01 : ‖w^2*x-w*z*u-w*y*v‖ ≤ 3*(k^2*l)-1/4 := by
      apply frontier_three_cubic_cofactor _ _ _ (k^2*l)
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds w x w k l hk hl hw' hx hw).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds z u w k l hk hl hz hu' hw).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds y v w k l hk hl hy hv' hw).2
    have h02 : ‖v^2*y-v*z*u-v*x*w‖ ≤ 3*(k^2*l)-1/4 := by
      apply frontier_three_cubic_cofactor _ _ _ (k^2*l)
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds v y v k l hk hl hv' hy hv).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds z u v k l hk hl hz hu' hv).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds x w v k l hk hl hx hw' hv).2
    have h03 : ‖u^2*z-u*y*v-u*x*w‖ ≤ 3*(k^2*l)-1/4 := by
      apply frontier_three_cubic_cofactor _ _ _ (k^2*l)
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds u z u k l hk hl hu' hz hu).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds y v u k l hk hl hy hv' hu).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds x w u k l hk hl hx hw' hu).2
    have h12 : ‖z^2*u-z*y*v-z*x*w‖ ≤ 3*(k^2*l)-1/4 := by
      apply frontier_three_cubic_cofactor _ _ _ (k^2*l)
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds z z u k l hk hl hz hz hu).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds z y v k l hk hl hz hy hv).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds z x w k l hk hl hz hx hw).2
    have h13 : ‖y^2*v-y*x*w-y*z*u‖ ≤ 3*(k^2*l)-1/4 := by
      apply frontier_three_cubic_cofactor _ _ _ (k^2*l)
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds y y v k l hk hl hy hy hv).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds y x w k l hk hl hy hx hw).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds y z u k l hk hl hy hz hu).2
    have h23 : ‖x^2*w-x*y*v-x*z*u‖ ≤ 3*(k^2*l)-1/4 := by
      apply frontier_three_cubic_cofactor _ _ _ (k^2*l)
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds x x w k l hk hl hx hx hw).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds x y v k l hk hl hx hy hv).2
      · simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
          (frontier_cubic_product_bounds x z u k l hk hl hx hz hu).2
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
