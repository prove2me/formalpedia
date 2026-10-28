-- Prove2me | solution 1 for D1Bound5.exists_integral_generator
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:42:39.758387+00:00
-- url     : https://prove2.me/submissions/5c94079d-2b68-44ee-8d43-0a876732d5c8

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_D1Bound5_integral_basis_one_gcd

section
open scoped NumberField
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K]




/-- A quadratic number ring has an integral basis of the form one, omega.
Bijectivity means that every algebraic integer, not just an order, has a
unique pair of integer coordinates in this basis. -/
theorem _root_.solution (hK : finrank ℚ K = 2) :
    ∃ w : 𝓞 K, Function.Bijective (fun p : ℤ × ℤ => (p.1 : 𝓞 K) + (p.2 : 𝓞 K)*w) := by
  classical
  let B := Module.finBasisOfFinrankEq ℤ (𝓞 K)
    ((NumberField.RingOfIntegers.rank K).trans hK)
  let a := B.repr 1 0
  let b := B.repr 1 1
  let u := Int.gcdA a b
  let v := Int.gcdB a b
  have hab : a*u+b*v = 1 := by
    have hg : Int.gcd a b = 1 := integral_basis_one_gcd hK B
    change a*Int.gcdA a b+b*Int.gcdB a b = 1
    rw [← Int.gcd_eq_gcd_ab, hg]
    rfl
  have hrep : (a : 𝓞 K)*B 0 + (b : 𝓞 K)*B 1 = 1 := by
    simpa [a, b, Fin.sum_univ_two, zsmul_eq_mul] using B.sum_repr (1 : 𝓞 K)
  let w : 𝓞 K := -v • B 0 + u • B 1
  have hform (n m : ℤ) :
      (n : 𝓞 K) + (m : 𝓞 K)*w =
        (a*n-v*m) • B 0 + (b*n+u*m) • B 1 := by
    calc
      _ = (n : 𝓞 K)*((a : 𝓞 K)*B 0 + (b : 𝓞 K)*B 1) + (m : 𝓞 K)*w := by
        rw [hrep, mul_one]
      _ = _ := by
        simp only [w, zsmul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg]
        ring
  refine ⟨w, ?_, ?_⟩
  · intro p q hpq
    change (p.1 : 𝓞 K)+(p.2 : 𝓞 K)*w = (q.1 : 𝓞 K)+(q.2 : 𝓞 K)*w at hpq
    rw [hform, hform] at hpq
    have h0 : a*p.1-v*p.2 = a*q.1-v*q.2 := by
      have h := congrArg (fun z : 𝓞 K => B.repr z 0) hpq
      simp only [map_add, map_smul] at h
      simpa using h
    have h1 : b*p.1+u*p.2 = b*q.1+u*q.2 := by
      have h := congrArg (fun z : 𝓞 K => B.repr z 1) hpq
      simp only [map_add, map_smul] at h
      simpa using h
    apply Prod.ext
    · linear_combination u*h0+v*h1-(p.1-q.1)*hab
    · linear_combination -b*h0+a*h1-(p.2-q.2)*hab
  · intro z
    let x := B.repr z 0
    let y := B.repr z 1
    refine ⟨(u*x+v*y, -b*x+a*y), ?_⟩
    dsimp only
    rw [hform]
    have hx : a*(u*x+v*y)-v*(-b*x+a*y) = x := by linear_combination x*hab
    have hy : b*(u*x+v*y)+u*(-b*x+a*y) = y := by linear_combination y*hab
    rw [hx, hy]
    simpa [x, y, Fin.sum_univ_two] using B.sum_repr z





end D1Bound5
end
