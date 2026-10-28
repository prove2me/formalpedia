-- Prove2me | solution 1 for D1Bound5.QuadInt.complex_generator_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:57.864053+00:00
-- url     : https://prove2.me/submissions/47c46490-1eb0-4926-9e85-e0ea36f5fb79

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5.QuadInt

open scoped QuadraticAlgebra

variable {tau nu : ℤ}



/-- A nonreal quadratic generator has real part tau/2 and norm nu. -/
theorem _root_.solution (f : QuadInt tau nu →+* ℂ)
    (hi : (f QuadraticAlgebra.omega).im ≠ 0) :
    2*(f QuadraticAlgebra.omega).re = (tau : ℝ) ∧
    (f QuadraticAlgebra.omega).re^2 + (f QuadraticAlgebra.omega).im^2 = (nu : ℝ) ∧
    (discriminant tau nu : ℝ) = 4*(f QuadraticAlgebra.omega).im^2 := by
  let w := f QuadraticAlgebra.omega
  have hrel : (QuadraticAlgebra.omega : QuadInt tau nu)*QuadraticAlgebra.omega =
      -(nu : QuadInt tau nu)+(tau : QuadInt tau nu)*QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega]
  have he := congrArg f hrel
  simp only [map_mul, map_add, map_neg, map_intCast] at he
  change w*w = -(nu : ℂ)+(tau : ℂ)*w at he
  have hr : w.re*w.re-w.im*w.im = -(nu : ℝ)+(tau : ℝ)*w.re := by
    simpa using congrArg Complex.re he
  have him : (2*w.re-(tau : ℝ))*w.im = 0 := by
    have h := congrArg Complex.im he
    simp only [Complex.mul_im, Complex.add_im, Complex.neg_im,
      Complex.intCast_im, Complex.intCast_re, neg_zero, zero_mul, zero_add, add_zero] at h
    nlinarith [h]
  have ht : 2*w.re = (tau : ℝ) := by
    have := (mul_eq_zero.mp him).resolve_right hi
    linarith
  have hn : w.re^2+w.im^2 = (nu : ℝ) := by
    linear_combination w.re*ht-hr
  refine ⟨ht, hn, ?_⟩
  change ((4*nu-tau^2 : ℤ) : ℝ) = 4*w.im^2
  push_cast
  linear_combination -4*hn+(2*w.re+(tau : ℝ))*ht







end D1Bound5.QuadInt
end
