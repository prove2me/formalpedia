-- Prove2me | solution 1 for CurveSymmetry.cartesianize_complexify
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:26.475069+00:00
-- url     : https://prove2.me/submissions/fc217458-0d20-4fad-b6d1-a52bbad0cd10

-- Solution generated from lean/CartesianCoordinates.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma complexify_C (c : ℂ) : complexify (C c) = C c := by simp [complexify]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma cartesianize_C (c : ℂ) : cartesianize (C c) = C c := by simp [cartesianize]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma complexify_X_zero : complexify (X 0) = C (1 / 2 : ℂ) * (X 0 + X 1) := by simp [complexify]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma complexify_X_one : complexify (X 1) = -C Complex.I * C (1 / 2 : ℂ) * (X 0 - X 1) := by simp [complexify]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma cartesianize_X_zero : cartesianize (X 0) = X 0 + C Complex.I * X 1 := by simp [cartesianize]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma cartesianize_X_one : cartesianize (X 1) = X 0 - C Complex.I * X 1 := by simp [cartesianize]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution (P : BPoly) : cartesianize (complexify P) = P := by
  have hI : (C Complex.I : BPoly) ^ 2 = -1 := by rw [← map_pow, Complex.I_sq]; simp
  have hhalf : (2 : BPoly) * C (1 / 2 : ℂ) = 1 := by
    have h := congrArg (C : ℂ →+* BPoly) (show (2 : ℂ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i
      · change P * cartesianize (complexify (X 0)) = P * X 0
        rw [complexify_X_zero, map_mul, cartesianize_C, map_add, cartesianize_X_zero, cartesianize_X_one]
        linear_combination P * (X 0 : BPoly) * hhalf
      · change P * cartesianize (complexify (X 1)) = P * X 1
        rw [complexify_X_one, map_mul, map_mul, map_neg, cartesianize_C, cartesianize_C,
          map_sub, cartesianize_X_zero, cartesianize_X_one]
        linear_combination P * (X 1 : BPoly) * hhalf -
          2 * P * (X 1 : BPoly) * C (1 / 2 : ℂ) * hI
end

#print axioms solution
