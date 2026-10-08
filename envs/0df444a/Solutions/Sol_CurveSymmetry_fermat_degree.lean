-- Prove2me | solution 1 for CurveSymmetry.fermat_degree
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:59.360115+00:00
-- url     : https://prove2.me/submissions/0c9061b4-e1e2-41f8-bfc3-ffa5fae9e71a

-- Solution generated from lean/Fermat.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
theorem solution {d : ℕ} (hd : 0 < d) : (fermatPolynomial d).totalDegree = d := by
  open MvPolynomial in
  have h0 : (fermatPolynomial d).coeff (exponent d 0) = 1 := by
    have h10 : (Finsupp.single (1 : Fin 2) d : Exponent) ≠ Finsupp.single 0 d := by
      intro h
      have he := congrArg (fun s : Exponent => s 0) h
      simp [hd.ne] at he
    have hzero : (0 : Exponent) ≠ Finsupp.single 0 d := by
      intro h
      have he := congrArg (fun s : Exponent => s 0) h
      simp [hd.ne] at he
    simp [fermatPolynomial, exponent, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.coeff_monomial, h10, hzero]
  have hlo := support_degree (MvPolynomial.mem_support_iff.mpr (by rw [h0]; exact one_ne_zero))
  simp only [exponent_zero, exponent_one, Nat.add_zero] at hlo
  have hsum := MvPolynomial.totalDegree_add (MvPolynomial.X 0 ^ d : BPoly) (MvPolynomial.X 1 ^ d)
  have hsub := MvPolynomial.totalDegree_sub_C_le
    (MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d : BPoly) 2
  simp only [MvPolynomial.totalDegree_X_pow, max_self] at hsum
  change (MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d - MvPolynomial.C 2 : BPoly).totalDegree = d
  change d ≤ (MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d - MvPolynomial.C 2 : BPoly).totalDegree at hlo
  omega
end

#print axioms solution
