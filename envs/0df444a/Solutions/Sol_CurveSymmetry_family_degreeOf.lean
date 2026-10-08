-- Prove2me | solution 1 for CurveSymmetry.family_degreeOf
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:38.431166+00:00
-- url     : https://prove2.me/submissions/10d2232c-c904-44c5-ba35-828fbeb30f20

-- Solution generated from lean/FamilyBidegree.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma family_fourTerm (m : ℕ) (α : ℂ) :
    familyPolynomial m α = fourTermForm m α (star α) 1 1 := by
  simp only [familyPolynomial, fourTermForm, binaryForm, map_one, one_mul]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma fourTermForm_monomial (m : ℕ) (a b c d : ℂ) :
    fourTermForm m a b c d = monomial (exponent m 0) a + monomial (exponent 0 m) b +
      monomial (exponent (m + 1) 1) c + monomial (exponent 1 (m + 1)) d := by
  simp only [fourTermForm, binaryForm, monomial_exponent, pow_zero, pow_succ, mul_one]
  ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma fourTermForm_coefficients {m : ℕ} (hm : 0 < m) (a b c d : ℂ) :
    (fourTermForm m a b c d).coeff (exponent m 0) = a ∧
      (fourTermForm m a b c d).coeff (exponent 0 m) = b ∧
      (fourTermForm m a b c d).coeff (exponent (m + 1) 1) = c ∧
      (fourTermForm m a b c d).coeff (exponent 1 (m + 1)) = d := by
  rw [fourTermForm_monomial]
  simp [coeff_monomial, exponent_eq_iff, hm.ne']
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma degree_add_bound (i : Fin 2) {p q : BPoly} {n : ℕ}
    (hp : p.degreeOf i ≤ n) (hq : q.degreeOf i ≤ n) : (p + q).degreeOf i ≤ n :=
  (degreeOf_add_le i p q).trans (max_le hp hq)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma degree_mul_bound (i : Fin 2) {p q : BPoly} {a b : ℕ}
    (hp : p.degreeOf i ≤ a) (hq : q.degreeOf i ≤ b) : (p * q).degreeOf i ≤ a + b :=
  (degreeOf_mul_le i p q).trans (Nat.add_le_add hp hq)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma degree_pow_bound (i : Fin 2) {p : BPoly} {a : ℕ}
    (hp : p.degreeOf i ≤ a) (n : ℕ) : (p ^ n).degreeOf i ≤ n * a :=
  (degreeOf_pow_le i p n).trans (Nat.mul_le_mul_left n hp)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma degree_affine_bound (i j : Fin 2) (a b : ℂ) :
    (C a * X j + C b : BPoly).degreeOf i ≤ if i = j then 1 else 0 := by
  calc
    _ ≤ max ((C a * X j : BPoly).degreeOf i) ((C b : BPoly).degreeOf i) :=
      degreeOf_add_le i _ _
    _ ≤ max ((X j : BPoly).degreeOf i) 0 :=
      max_le_max (degreeOf_C_mul_le _ i a) (by simp)
    _ = _ := by simp [degreeOf_X]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
private lemma biform_degree_bound (i : Fin 2) (m : ℕ) (β : ℂ)
    (u v s t : BPoly) {a b : ℕ} (hu : u.degreeOf i ≤ a) (hv : v.degreeOf i ≤ a)
    (hs : s.degreeOf i ≤ b) (ht : t.degreeOf i ≤ b) :
    (C β * u ^ m * v * t ^ (m + 1) + u ^ (m + 1) * s * t ^ m +
      C (star β) * v ^ (m + 1) * s ^ m * t + u * v ^ m * s ^ (m + 1)).degreeOf i ≤
        (m + 1) * (a + b) := by
  apply degree_add_bound i (degree_add_bound i (degree_add_bound i ?_ ?_) ?_) ?_
  · have h := degree_mul_bound i (degree_mul_bound i
      ((degreeOf_C_mul_le _ i β).trans (degree_pow_bound i hu m)) hv)
      (degree_pow_bound i ht (m + 1))
    convert h using 1
    ring
  · have h := degree_mul_bound i (degree_mul_bound i (degree_pow_bound i hu (m + 1)) hs)
      (degree_pow_bound i ht m)
    convert h using 1
    ring
  · have h := degree_mul_bound i (degree_mul_bound i
      ((degreeOf_C_mul_le _ i (star β)).trans (degree_pow_bound i hv (m + 1)))
      (degree_pow_bound i hs m)) ht
    convert h using 1
    ring
  · have h := degree_mul_bound i (degree_mul_bound i hu (degree_pow_bound i hv m))
      (degree_pow_bound i hs (m + 1))
    convert h using 1
    ring
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
/-- Arbitrary product-projective pullback never exceeds degree `m+1` in either
affine variable. The total degree can be larger than the source total degree. -/
theorem familyMobiusPullback_degreeOf_le (m : ℕ) (β : ℂ) (g : MobiusMatrix) (i : Fin 2) :
    (familyMobiusPullback m β g).degreeOf i ≤ m + 1 := by
  have h := biform_degree_bound i m β (mobiusX g 0) (mobiusX g 1) (mobiusY g 0) (mobiusY g 1)
    (degree_affine_bound i 0 (g 0 0) (g 0 1))
    (degree_affine_bound i 0 (g 1 0) (g 1 1))
    (degree_affine_bound i 1 (star (g 0 0)) (star (g 0 1)))
    (degree_affine_bound i 1 (star (g 1 0)) (star (g 1 1)))
  fin_cases i <;> simpa [familyMobiusPullback] using h
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
lemma familyMobiusPullback_one (m : ℕ) (α : ℂ) :
    familyMobiusPullback m α 1 = familyPolynomial m α := by
  simp [familyMobiusPullback, mobiusX, mobiusY, familyPolynomial, pow_succ]
  ring
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
open OnePoint
theorem solution {m : ℕ} (hm : 0 < m) (α : ℂ) (i : Fin 2) :
    (familyPolynomial m α).degreeOf i = m + 1 := by
  apply Nat.le_antisymm
  · rw [← familyMobiusPullback_one m α]
    exact familyMobiusPullback_degreeOf_le m α 1 i
  · have hcoeff := fourTermForm_coefficients hm α (star α) 1 1
    rw [← family_fourTerm] at hcoeff
    fin_cases i
    · have hs : exponent (m + 1) 1 ∈ (familyPolynomial m α).support := by
        rw [mem_support_iff, hcoeff.2.2.1]
        exact one_ne_zero
      simpa [exponent] using monomial_le_degreeOf (0 : Fin 2) hs
    · have hs : exponent 1 (m + 1) ∈ (familyPolynomial m α).support := by
        rw [mem_support_iff, hcoeff.2.2.2]
        exact one_ne_zero
      simpa [exponent] using monomial_le_degreeOf (1 : Fin 2) hs
end

#print axioms solution
