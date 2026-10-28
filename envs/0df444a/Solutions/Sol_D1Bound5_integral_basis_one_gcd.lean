-- Prove2me | solution 1 for D1Bound5.integral_basis_one_gcd
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:15.823328+00:00
-- url     : https://prove2.me/submissions/1943e542-cc86-4df4-8fc0-3e4dccd93703

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K]

/-- The two coordinates of one in any integral basis are coprime. -/
theorem _root_.solution (hK : finrank ℚ K = 2)
    (B : Basis (Fin 2) ℤ (𝓞 K)) :
    Int.gcd (B.repr 1 0) (B.repr 1 1) = 1 := by
  let a := B.repr 1 0
  let b := B.repr 1 1
  let d := Int.gcd a b
  obtain ⟨p, hp⟩ := Int.gcd_dvd_left a b
  obtain ⟨q, hq⟩ := Int.gcd_dvd_right a b
  let z : 𝓞 K := p • B 0 + q • B 1
  have hrep : a • B 0 + b • B 1 = 1 := by
    simpa [a, b, Fin.sum_univ_two] using B.sum_repr (1 : 𝓞 K)
  have hdz : (d : 𝓞 K) * z = 1 := by
    calc
      (d : 𝓞 K) * z = ((d : ℤ)*p) • B 0 + ((d : ℤ)*q) • B 1 := by
        simp only [z, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_add, mul_assoc]
      _ = a • B 0 + b • B 1 :=
        congrArg₂ (· + ·) (congrArg (fun n : ℤ => n • B 0) hp.symm)
          (congrArg (fun n : ℤ => n • B 1) hq.symm)
      _ = 1 := hrep
  have hdim : finrank ℤ (𝓞 K) = 2 := (NumberField.RingOfIntegers.rank K).trans hK
  have hnorm : (d : ℤ)^2 * Algebra.norm ℤ z = 1 := by
    have h := congrArg (Algebra.norm ℤ) hdz
    simpa only [map_mul, Algebra.norm_natCast, hdim, map_one] using h
  have hdvd : (d : ℤ) ∣ 1 := ⟨(d : ℤ) * Algebra.norm ℤ z, by nlinarith [hnorm]⟩
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hdvd)








end D1Bound5
end
