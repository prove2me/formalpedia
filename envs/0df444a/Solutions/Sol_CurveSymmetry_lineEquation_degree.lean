-- Prove2me | solution 1 for CurveSymmetry.lineEquation_degree
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:11.622862+00:00
-- url     : https://prove2.me/submissions/2cfd66c8-862c-4480-9324-a5225cc41ace

-- Solution generated from lean/Translation.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution (z v : ℂ) (hv : v ≠ 0) : (lineEquation z v).totalDegree = 1 := by
  have h0 := totalDegree_mul (C (star v) : BPoly) (X 0)
  have h1 := totalDegree_mul (C v : BPoly) (X 1)
  have h2 := totalDegree_sub (C (star v) * X 0 : BPoly) (C v * X 1)
  have h3 := totalDegree_sub_C_le (C (star v) * X 0 - C v * X 1 : BPoly)
    (star v * z - v * star z)
  simp only [totalDegree_C, totalDegree_X, zero_add] at h0 h1
  have hne : (Finsupp.single (1 : Fin 2) 1 : Exponent) ≠ Finsupp.single 0 1 := by
    intro h
    have := congrArg (fun s : Exponent => s 0) h
    simp at this
  have hn0 : (0 : Exponent) ≠ Finsupp.single 0 1 := by
    intro h
    have := congrArg (fun s : Exponent => s 0) h
    simp at this
  have hc : (lineEquation z v).coeff (exponent 1 0) = star v := by
    simp [lineEquation, exponent, coeff_C_mul, coeff_X, hne, hn0]
  have hs : exponent 1 0 ∈ (lineEquation z v).support := by
    rw [mem_support_iff, hc]
    exact star_ne_zero.mpr hv
  have h4 := support_degree hs
  simp only [exponent_zero, exponent_one, add_zero] at h4
  change (C (star v) * X 0 - C v * X 1 - C (star v * z - v * star z) : BPoly).totalDegree = 1
  change 1 ≤ (C (star v) * X 0 - C v * X 1 - C (star v * z - v * star z) : BPoly).totalDegree at h4
  omega
end

#print axioms solution
