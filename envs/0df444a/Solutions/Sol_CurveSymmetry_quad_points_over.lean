-- Prove2me | solution 1 for CurveSymmetry.quad_points_over
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:26.255915+00:00
-- url     : https://prove2.me/submissions/adf359ee-70bc-40d0-a1a5-e2055dfe1d96

-- Solution generated from lean/QuadraticPlaces.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X])
theorem solution (c : ℂ) :
    (h.eval c ≠ 0 → ∃ d₀ : ℂ, d₀ ≠ -d₀ ∧ ∀ d : ℂ, d ^ 2 = h.eval c ↔ d = d₀ ∨ d = -d₀) ∧
      (h.eval c = 0 → ∀ d : ℂ, d ^ 2 = h.eval c ↔ d = 0) := by
  refine ⟨fun hc => ?_, fun hc d => ?_⟩
  · obtain ⟨d₀, hd₀⟩ := IsAlgClosed.exists_pow_nat_eq (h.eval c) two_pos
    have h0 : d₀ ≠ 0 := by
      rintro rfl
      exact hc (by simpa using hd₀.symm)
    refine ⟨d₀, fun hn => h0 (by linear_combination hn / 2), fun d => ?_⟩
    rw [← hd₀, sq_eq_sq_iff_eq_or_eq_neg]
  · rw [hc, pow_eq_zero_iff two_ne_zero]
end

#print axioms solution
