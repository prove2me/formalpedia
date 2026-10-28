-- Prove2me | solution 1 for D1Bound5.crossBlock_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:41:38.577676+00:00
-- url     : https://prove2.me/submissions/93171a4d-eb18-4ff8-8eea-fa417d75e4bd

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
import Theorems.Thm_D1Bound5_crossBlock_growth_of_scaled_determinant
import Theorems.Thm_D1Bound5_crossBlock_ordered_error_det_upper
import Theorems.Thm_D1Bound5_crossBlock_rootMatrix_det_ne_zero
import Theorems.Thm_D1Bound5_crossBlock_scaled_det_norm_sq
import Theorems.Thm_D1Bound5_exists_crossBlock_signed_scaled_error

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5





/-- Quantitative cross-block growth over any characteristic-zero domain
whose nonzero elements have complex modulus at least one. The following
full-ring corollary supplies this arithmetic property unconditionally. -/
theorem _root_.solution
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (f : R →+* ℂ) (hdiscrete : ∀ x : R, x ≠ 0 → 1 ≤ ‖f x‖)
    (a b : Fin 3 → R) (M : Fin 3 → Fin 3 → R)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hroot : ∀ i j, (M i j)^2 = a i*b j+1)
    (hmonA : Monotone (fun i => ‖f (a i)‖))
    (hmonB : Monotone (fun i => ‖f (b i)‖))
    (hlarge : 9 ≤ ‖f (a 0)‖*‖f (b 0)‖) :
    (‖f (a 0)‖*‖f (b 0)‖)^3*(‖f (a 1)‖*‖f (b 1)‖)/7 <
      ‖f (a 2)‖*‖f (b 2)‖ := by
  have hlargeij (i j : Fin 3) : 9 ≤ ‖f (a i)*f (b j)‖ := by
    rw [norm_mul]
    exact hlarge.trans (mul_le_mul (hmonA (by omega : 0 ≤ i))
      (hmonB (by omega : 0 ≤ j)) (norm_nonneg _) (norm_nonneg _))
  obtain ⟨u, v, S, hu, hv, hS, herr⟩ :=
    exists_crossBlock_signed_scaled_error f a b M hroot hlargeij
  let T : Fin 3 → Fin 3 → ℂ :=
    fun i j => (f (a i)*u i)*f (S i j)*(f (b j)*v j)
  let E : Fin 3 → Fin 3 → ℂ := fun i j =>
    T i j-(f (a i)*f (b j))^2-(1/2 : ℂ)*(f (a i)*f (b j))
  have hE (i j : Fin 3) : ‖E i j‖ ≤ (2/15 : ℝ) := by
    have hrewrite : E i j = (f (a i)*f (b j))*(u i*f (S i j)*v j)-
        (f (a i)*f (b j))^2-(1/2 : ℂ)*(f (a i)*f (b j)) := by
      dsimp [E, T]
      ring
    rw [hrewrite]
    exact (herr i j).le
  have hTform : T = fun i j =>
      (f (a i)*f (b j))^2+(1/2 : ℂ)*(f (a i)*f (b j))+E i j := by
    ext i j
    dsimp only [E]
    ring
  have hWi (i : Fin 3) : 9 ≤ ‖f (a i)‖*‖f (b i)‖ := by
    simpa only [norm_mul] using hlargeij i i
  have hupper : ‖(Matrix.det (Matrix.of T))‖ <
      (5/2 : ℝ)*(‖f (a 2)‖*‖f (b 2)‖)^2*(‖f (a 1)‖*‖f (b 1)‖) := by
    rw [hTform]
    exact crossBlock_ordered_error_det_upper
      (fun i => f (a i)) (fun i => f (b i)) E hmonA hmonB hE (hWi 1) (hWi 2)
  have hnorm : 1 ≤ ‖f (Matrix.det (Matrix.of S))‖ :=
    hdiscrete (Matrix.det (Matrix.of S)) (crossBlock_rootMatrix_det_ne_zero a b (Matrix.of S) ha hb hS)
  have hnormsq : 1 ≤ ‖f (Matrix.det (Matrix.of S))‖^2 := by nlinarith only [hnorm]
  have hlower : ((‖f (a 0)‖*‖f (b 0)‖)*(‖f (a 1)‖*‖f (b 1)‖)*
      (‖f (a 2)‖*‖f (b 2)‖))^3 ≤ ‖(Matrix.det (Matrix.of T))‖^2 := by
    rw [crossBlock_scaled_det_norm_sq f a b u v S hu hv]
    exact le_mul_of_one_le_right (by positivity) hnormsq
  exact crossBlock_growth_of_scaled_determinant
    (‖f (a 0)‖*‖f (b 0)‖) (‖f (a 1)‖*‖f (b 1)‖)
    (‖f (a 2)‖*‖f (b 2)‖) ‖(Matrix.det (Matrix.of T))‖
    (hWi 0) (hWi 1) (hWi 2) (norm_nonneg _) hlower hupper





end D1Bound5
end
