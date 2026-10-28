-- Prove2me | solution 1 for D1Bound5.norm_sq_full_ring_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:37:07.380767+00:00
-- url     : https://prove2.me/submissions/dd0ebe72-0003-4cfb-b21b-d74ed54557f6

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_complex_generator_parameters
import Theorems.Thm_D1Bound5_QuadInt_complex_image
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_full_ring_generator_nonreal

section
namespace D1Bound5.QuadInt

open scoped QuadraticAlgebra

variable {tau nu : ℤ}







/-- The coordinate norm equals the squared complex modulus. -/
theorem norm_sq_complex_image (f : QuadInt tau nu →+* ℂ)
    (hi : (f QuadraticAlgebra.omega).im ≠ 0) (z : QuadInt tau nu) :
    ‖f z‖^2 = (z.norm : ℝ) := by
  obtain ⟨ht, hn, _⟩ := complex_generator_parameters f hi
  rw [complex_image f z, Complex.sq_norm, Complex.normSq_apply, norm_formula]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, zero_mul, zero_add, sub_zero]
  push_cast
  linear_combination (z.im : ℝ)^2*hn + (z.re : ℝ)*(z.im : ℝ)*ht



end D1Bound5.QuadInt
end

section
open scoped NumberField ComplexConjugate
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]





/-- The actual complex modulus in the field agrees with the integral
coordinate norm under any full-ring equivalence and any complex embedding. -/
theorem _root_.solution {tau nu : ℤ}
    (e : QuadInt tau nu ≃+* 𝓞 K) (φ : K →+* ℂ) (z : QuadInt tau nu) :
    ‖φ (e z : K)‖^2 = (z.norm : ℝ) := by
  exact QuadInt.norm_sq_complex_image _ (full_ring_generator_nonreal e φ) z





end D1Bound5
end
