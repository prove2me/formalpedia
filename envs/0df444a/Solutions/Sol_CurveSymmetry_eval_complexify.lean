-- Prove2me | solution 1 for CurveSymmetry.eval_complexify
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:32.857351+00:00
-- url     : https://prove2.me/submissions/7ee23bbb-1988-4157-bbbc-3b44c489eaac

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
@[simp] lemma complexify_X_zero : complexify (X 0) = C (1 / 2 : ℂ) * (X 0 + X 1) := by simp [complexify]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
@[simp] lemma complexify_X_one : complexify (X 1) = -C Complex.I * C (1 / 2 : ℂ) * (X 0 - X 1) := by simp [complexify]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution (P : BPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (complexify P) =
      eval (fun i : Fin 2 => if i = 0 then (z.re : ℂ) else (z.im : ℂ)) P := by
  have hsum : z + star z = 2 * (z.re : ℂ) := by simpa using Complex.add_conj z
  have hsub : z - star z = 2 * (z.im : ℂ) * Complex.I := by simpa using Complex.sub_conj z
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      congr 1
      fin_cases i
      · change eval (fun j : Fin 2 => if j = 0 then z else star z) (complexify (X 0)) =
          eval (fun j : Fin 2 => if j = 0 then (z.re : ℂ) else (z.im : ℂ)) (X 0)
        rw [complexify_X_zero]
        simp only [map_mul, map_add, eval_C, eval_X, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hsum]
        ring
      · change eval (fun j : Fin 2 => if j = 0 then z else star z) (complexify (X 1)) =
          eval (fun j : Fin 2 => if j = 0 then (z.re : ℂ) else (z.im : ℂ)) (X 1)
        rw [complexify_X_one]
        simp only [map_mul, map_sub, map_neg, eval_C, eval_X, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hsub]
        ring_nf
        rw [Complex.I_sq]
        ring
end

#print axioms solution
