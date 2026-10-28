-- Prove2me | solution 1 for D1Bound5.crossBlock_quadratic_linear_error_det_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:43:11.867015+00:00
-- url     : https://prove2.me/submissions/1f36d330-e823-4a9d-9df5-e8ed819ec4b9

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_CrossBlockUpper_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5

private theorem crossBlock_norm_add_three (x y z : ℂ) (X Y Z : ℝ)
    (hx : ‖x‖ ≤ X) (hy : ‖y‖ ≤ Y) (hz : ‖z‖ ≤ Z) :
    ‖x+y+z‖ ≤ X+Y+Z := by
  calc
    ‖x+y+z‖ ≤ ‖x+y‖+‖z‖ := norm_add_le _ _
    _ ≤ (‖x‖+‖y‖)+‖z‖ := add_le_add (norm_add_le x y) le_rfl
    _ ≤ X+Y+Z := add_le_add (add_le_add hx hy) hz



private theorem crossBlock_keptProduct_norm_le (x e : Fin 3 → ℂ)
    (M P c : ℝ) (hM : 0 ≤ M) (hP : 0 ≤ P) (hc : 0 ≤ c)
    (hx : ∀ i, ‖x i‖ ≤ M)
    (hpair : ∀ i j, i ≠ j → ‖(x i)^2*x j‖ ≤ P)
    (he : ∀ i, ‖e i‖ ≤ c) :
    ‖crossBlock_keptProduct x e‖ ≤
      c^3+3*M^2*c^2+(3/2 : ℝ)*M*c^2+3*P*c := by
  have h0 : ‖e 0*e 1*e 2‖ ≤ c^3 := by
    rw [norm_mul, norm_mul]
    calc
      ‖e 0‖*‖e 1‖*‖e 2‖ ≤ c*c*c := by gcongr <;> apply he
      _ = c^3 := by ring
  have hquad (i j k : Fin 3) : ‖(x i)^2*e j*e k‖ ≤ M^2*c^2 := by
    rw [norm_mul, norm_mul, norm_pow]
    calc
      ‖x i‖^2*‖e j‖*‖e k‖ ≤ M^2*c*c := by gcongr <;> first | apply hx | apply he
      _ = M^2*c^2 := by ring
  have hlinear (i j k : Fin 3) : ‖x i*e j*e k‖ ≤ M*c^2 := by
    rw [norm_mul, norm_mul]
    calc
      ‖x i‖*‖e j‖*‖e k‖ ≤ M*c*c := by gcongr <;> first | apply hx | apply he
      _ = M*c^2 := by ring
  have hmixed (i j k : Fin 3) (hij : i ≠ j) :
      ‖(x i)^2*x j*e k‖ ≤ P*c := by
    rw [norm_mul]
    exact mul_le_mul (hpair i j hij) (he k) (norm_nonneg _) hP
  have hq : ‖x 0^2*e 1*e 2+x 1^2*e 0*e 2+x 2^2*e 0*e 1‖ ≤
      3*M^2*c^2 := by
    calc
      _ ≤ M^2*c^2+M^2*c^2+M^2*c^2 :=
        crossBlock_norm_add_three _ _ _ _ _ _ (hquad 0 1 2) (hquad 1 0 2) (hquad 2 0 1)
      _ = 3*M^2*c^2 := by ring
  have hl : ‖(1/2 : ℂ)*(x 0*e 1*e 2+x 1*e 0*e 2+x 2*e 0*e 1)‖ ≤
      (3/2 : ℝ)*M*c^2 := by
    have hs := crossBlock_norm_add_three _ _ _ _ _ _
      (hlinear 0 1 2) (hlinear 1 0 2) (hlinear 2 0 1)
    calc
      _ = (1/2 : ℝ)*‖x 0*e 1*e 2+x 1*e 0*e 2+x 2*e 0*e 1‖ := by
        norm_num [norm_mul]
      _ ≤ (1/2 : ℝ)*(M*c^2+M*c^2+M*c^2) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = (3/2 : ℝ)*M*c^2 := by ring
  have hm : ‖(1/2 : ℂ)*(x 0^2*x 1*e 2+x 0^2*x 2*e 1+x 1^2*x 0*e 2+
      x 1^2*x 2*e 0+x 2^2*x 0*e 1+x 2^2*x 1*e 0)‖ ≤ 3*P*c := by
    have hleft := crossBlock_norm_add_three _ _ _ _ _ _
      (hmixed 0 1 2 (by decide)) (hmixed 0 2 1 (by decide)) (hmixed 1 0 2 (by decide))
    have hright := crossBlock_norm_add_three _ _ _ _ _ _
      (hmixed 1 2 0 (by decide)) (hmixed 2 0 1 (by decide)) (hmixed 2 1 0 (by decide))
    have hs : ‖x 0^2*x 1*e 2+x 0^2*x 2*e 1+x 1^2*x 0*e 2+
        x 1^2*x 2*e 0+x 2^2*x 0*e 1+x 2^2*x 1*e 0‖ ≤ 6*P*c := by
      calc
        _ = ‖(x 0^2*x 1*e 2+x 0^2*x 2*e 1+x 1^2*x 0*e 2)+
            (x 1^2*x 2*e 0+x 2^2*x 0*e 1+x 2^2*x 1*e 0)‖ := by congr 1 <;> ring
        _ ≤ ‖x 0^2*x 1*e 2+x 0^2*x 2*e 1+x 1^2*x 0*e 2‖+
            ‖x 1^2*x 2*e 0+x 2^2*x 0*e 1+x 2^2*x 1*e 0‖ := norm_add_le _ _
        _ ≤ (P*c+P*c+P*c)+(P*c+P*c+P*c) := add_le_add hleft hright
        _ = 6*P*c := by ring
    calc
      _ = (1/2 : ℝ)*‖x 0^2*x 1*e 2+x 0^2*x 2*e 1+x 1^2*x 0*e 2+
          x 1^2*x 2*e 0+x 2^2*x 0*e 1+x 2^2*x 1*e 0‖ := by norm_num [norm_mul]
      _ ≤ (1/2 : ℝ)*(6*P*c) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = 3*P*c := by ring
  unfold crossBlock_keptProduct
  calc
    _ ≤ ‖e 0*e 1*e 2+
        (x 0^2*e 1*e 2+x 1^2*e 0*e 2+x 2^2*e 0*e 1)+
        (1/2 : ℂ)*(x 0*e 1*e 2+x 1*e 0*e 2+x 2*e 0*e 1)‖+
        ‖(1/2 : ℂ)*(x 0^2*x 1*e 2+x 0^2*x 2*e 1+x 1^2*x 0*e 2+
          x 1^2*x 2*e 0+x 2^2*x 0*e 1+x 2^2*x 1*e 0)‖ := norm_add_le _ _
    _ ≤ (c^3+3*M^2*c^2+(3/2 : ℝ)*M*c^2)+3*P*c :=
      add_le_add (crossBlock_norm_add_three _ _ _ _ _ _ h0 hq hl) hm

/-- A finite determinant estimate for two rank-one layers plus a uniformly
bounded error matrix. No power series or limiting Cauchy--Binet identity
is needed. The pair hypothesis records distinct rows and columns. -/
theorem _root_.solution
    (a b : Fin 3 → ℂ) (E : Fin 3 → Fin 3 → ℂ)
    (M P c : ℝ) (hM : 0 ≤ M) (hP : 0 ≤ P) (hc : 0 ≤ c)
    (hentry : ∀ i j, ‖a i*b j‖ ≤ M)
    (hpair : ∀ i j k l, i ≠ j → k ≠ l →
      ‖(a i*b k)^2*(a j*b l)‖ ≤ P)
    (hE : ∀ i j, ‖E i j‖ ≤ c) :
    ‖Matrix.det (Matrix.of (fun i j => (a i*b j)^2+(1/2 : ℂ)*(a i*b j)+E i j))‖ ≤
      18*P*c+18*M^2*c^2+9*M*c^2+6*c^3 := by
  let t (p : Fin 3 → Fin 3) : ℂ :=
    crossBlock_keptProduct (fun i => a i*b (p i)) (fun i => E i (p i))
  let C : ℝ := c^3+3*M^2*c^2+(3/2 : ℝ)*M*c^2+3*P*c
  have ht (p : Fin 3 → Fin 3) (hp : Function.Injective p) : ‖t p‖ ≤ C := by
    apply crossBlock_keptProduct_norm_le _ _ M P c hM hP hc
    · intro i; exact hentry i (p i)
    · intro i j hij; exact hpair i j (p i) (p j) hij (hp.ne hij)
    · intro i; exact hE i (p i)
  have hid :
      Matrix.det (Matrix.of (fun i j => (a i*b j)^2+(1/2 : ℂ)*(a i*b j)+E i j)) =
      (t ![0,1,2]+t ![1,2,0]+t ![2,0,1])-
        (t ![0,2,1]+t ![1,0,2]+t ![2,1,0]) := by
    rw [Matrix.det_fin_three]
    simp [t, crossBlock_keptProduct]
    <;> ring
  rw [hid]
  calc
    _ ≤ ‖t ![0,1,2]+t ![1,2,0]+t ![2,0,1]‖+
        ‖t ![0,2,1]+t ![1,0,2]+t ![2,1,0]‖ := norm_sub_le _ _
    _ ≤ (C+C+C)+(C+C+C) := add_le_add
      (crossBlock_norm_add_three _ _ _ _ _ _
        (ht ![0,1,2] (by decide)) (ht ![1,2,0] (by decide)) (ht ![2,0,1] (by decide)))
      (crossBlock_norm_add_three _ _ _ _ _ _
        (ht ![0,2,1] (by decide)) (ht ![1,0,2] (by decide)) (ht ![2,1,0] (by decide)))
    _ = 18*P*c+18*M^2*c^2+9*M*c^2+6*c^3 := by dsimp [C]; ring

end D1Bound5
end
