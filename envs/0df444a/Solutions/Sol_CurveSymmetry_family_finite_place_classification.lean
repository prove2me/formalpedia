-- Prove2me | solution 1 for CurveSymmetry.family_finite_place_classification
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:45.068999+00:00
-- url     : https://prove2.me/submissions/0de2d41f-12fc-4d97-a9b1-b5eb893d3e8a

-- Solution generated from lean/QuadraticPlaces.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Theorems.Thm_CurveSymmetry_quad_finite_place_classification
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
theorem solution {m : ℕ} {α : ℂ} [Fact (0 < m)]
    [Fact (α ≠ star α)] :
    (∀ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), quadPlace (familyH m α) c d hd ≠ ⊤ ∧
        ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField (familyH m α)) p ∈
          quadPlace (familyH m α) c d hd) ∧
      (∀ O : ValuationSubring (QuadField (familyH m α)), O ≠ ⊤ →
        (∀ p : ℂ[X], algebraMap ℂ[X] (QuadField (familyH m α)) p ∈ O) →
          ∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd) ∧
      (∀ (c d c' d' : ℂ) (hd : d ^ 2 = (familyH m α).eval c)
        (hd' : d' ^ 2 = (familyH m α).eval c'),
        quadPlace (familyH m α) c d hd = quadPlace (familyH m α) c' d' hd' → c = c' ∧ d = d') :=
  quad_finite_place_classification (familyH m α)
end

#print axioms solution
