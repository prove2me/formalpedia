-- Prove2me | solution 1 for D1Bound5.crossBlock_ordered_error_det_upper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:58:58.187659+00:00
-- url     : https://prove2.me/submissions/cfa1050e-088d-438b-8d50-27a07b178fa7

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
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
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_crossBlock_quadratic_linear_error_det_upper

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5

private theorem crossBlock_ordered_pair_le
    (A : Fin 3 → ℝ) (hA0 : ∀ i, 0 ≤ A i) (hA : Monotone A)
    (i j : Fin 3) (hij : i ≠ j) : A i*A j ≤ A 1*A 2 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact mul_le_mul (hA (by omega : i ≤ 1)) (hA (by omega : j ≤ 2))
      (hA0 j) (hA0 1)
  · rw [mul_comm (A i) (A j)]
    exact mul_le_mul (hA (by omega : j ≤ 1)) (hA (by omega : i ≤ 2))
      (hA0 i) (hA0 1)

private theorem crossBlock_ordered_cubic_le
    (A : Fin 3 → ℝ) (hA0 : ∀ i, 0 ≤ A i) (hA : Monotone A)
    (i j : Fin 3) (hij : i ≠ j) : (A i)^2*A j ≤ (A 2)^2*A 1 := by
  calc
    (A i)^2*A j = A i*(A i*A j) := by ring
    _ ≤ A 2*(A 1*A 2) := mul_le_mul (hA (by omega : i ≤ 2))
      (crossBlock_ordered_pair_le A hA0 hA i j hij)
      (mul_nonneg (hA0 i) (hA0 j)) (hA0 2)
    _ = (A 2)^2*A 1 := by ring

/-- The finite rank-layer estimate specialized to ordered complex moduli.
The constant two fifteenths is a strict upper bound for 128/961 supplied
by the algebraic square-root perturbation estimate. -/
theorem _root_.solution
    (a b : Fin 3 → ℂ) (E : Fin 3 → Fin 3 → ℂ)
    (ha : Monotone (fun i => ‖a i‖)) (hb : Monotone (fun i => ‖b i‖))
    (hE : ∀ i j, ‖E i j‖ ≤ (2/15 : ℝ))
    (hW1 : 9 ≤ ‖a 1‖*‖b 1‖) (hW2 : 9 ≤ ‖a 2‖*‖b 2‖) :
    ‖Matrix.det (Matrix.of (fun i j => (a i*b j)^2+(1/2 : ℂ)*(a i*b j)+E i j))‖ <
      (5/2 : ℝ)*(‖a 2‖*‖b 2‖)^2*(‖a 1‖*‖b 1‖) := by
  let M : ℝ := ‖a 2‖*‖b 2‖
  let V : ℝ := ‖a 1‖*‖b 1‖
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hV : 0 ≤ V := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hentry (i j : Fin 3) : ‖a i*b j‖ ≤ M := by
    rw [norm_mul]
    exact mul_le_mul (ha (by omega : i ≤ 2)) (hb (by omega : j ≤ 2))
      (norm_nonneg _) (norm_nonneg _)
  have hpair (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l) :
      ‖(a i*b k)^2*(a j*b l)‖ ≤ M^2*V := by
    rw [norm_mul, norm_pow, norm_mul, norm_mul]
    calc
      (‖a i‖*‖b k‖)^2*(‖a j‖*‖b l‖) =
          (‖a i‖^2*‖a j‖)*(‖b k‖^2*‖b l‖) := by ring
      _ ≤ (‖a 2‖^2*‖a 1‖)*(‖b 2‖^2*‖b 1‖) :=
        mul_le_mul
          (crossBlock_ordered_cubic_le _ (fun _ => norm_nonneg _) ha i j hij)
          (crossBlock_ordered_cubic_le _ (fun _ => norm_nonneg _) hb k l hkl)
          (by positivity) (by positivity)
      _ = M^2*V := by dsimp [M, V]; ring
  have hup := crossBlock_quadratic_linear_error_det_upper a b E M (M^2*V)
    (2/15) hM (mul_nonneg (sq_nonneg _) hV) (by norm_num) hentry hpair hE
  have h9M : 9 ≤ M := hW2
  have h9V : 9 ≤ V := hW1
  have hprod : 9*M^2 ≤ M^2*V := by
    nlinarith only [mul_nonneg (sq_nonneg M) (sub_nonneg.mpr h9V)]
  have hMlow : 81 ≤ M^2 := by nlinarith only [h9M, sq_nonneg (M-9)]
  have hMlin : 9*M ≤ M^2 := by
    nlinarith only [mul_nonneg hM (sub_nonneg.mpr h9M)]
  have hnumeric :
      18*(M^2*V)*(2/15)+18*M^2*(2/15)^2+9*M*(2/15)^2+6*(2/15)^3 <
      (5/2 : ℝ)*M^2*V := by
    nlinarith only [hprod, hMlow, hMlin]
  exact hup.trans_lt hnumeric





end D1Bound5
end
