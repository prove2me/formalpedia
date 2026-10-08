-- Prove2me | solution 1 for CurveSymmetry.fourTermForm_proportional_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:01.804173+00:00
-- url     : https://prove2.me/submissions/9f04aa19-fb34-4d28-afb4-a61e427f125f

-- Solution generated from lean/FamilyTransport.lean (curve-symmetry-lean): inlined helpers in
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

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {m : ℕ} (hm : 0 < m) (a b c d A B C' D k : ℂ) :
    fourTermForm m a b c d = C k * fourTermForm m A B C' D ↔
      a = k * A ∧ b = k * B ∧ c = k * C' ∧ d = k * D := by
  constructor
  · intro h
    have h0 := congrArg (fun p : BPoly => p.coeff (exponent m 0)) h
    have h1 := congrArg (fun p : BPoly => p.coeff (exponent 0 m)) h
    have h2 := congrArg (fun p : BPoly => p.coeff (exponent (m + 1) 1)) h
    have h3 := congrArg (fun p : BPoly => p.coeff (exponent 1 (m + 1))) h
    obtain ⟨ha, hb, hc, hd⟩ := fourTermForm_coefficients hm a b c d
    obtain ⟨hA, hB, hC, hD⟩ := fourTermForm_coefficients hm A B C' D
    rw [ha, coeff_C_mul, hA] at h0
    rw [hb, coeff_C_mul, hB] at h1
    rw [hc, coeff_C_mul, hC] at h2
    rw [hd, coeff_C_mul, hD] at h3
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp only [fourTermForm, binaryForm, map_mul]
    ring
end

#print axioms solution
