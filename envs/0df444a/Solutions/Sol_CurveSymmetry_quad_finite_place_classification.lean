-- Prove2me | solution 1 for CurveSymmetry.quad_finite_place_classification
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:23.680951+00:00
-- url     : https://prove2.me/submissions/9b6863ca-65a3-4f3e-bbda-b16c1f956e69

-- Solution generated from lean/QuadraticPlaces.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Theorems.Thm_CurveSymmetry_eq_primeValuationSubring_placeCenter
import Theorems.Thm_CurveSymmetry_placeCenter_primeValuationSubring
import Theorems.Thm_CurveSymmetry_primeValuationSubring_ne_top
import Theorems.Thm_CurveSymmetry_quadEval_ker_injective
import Theorems.Thm_CurveSymmetry_quadRing_isMaximal_iff
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

namespace CurveSymmetry
set_option autoImplicit false
open IsLocalRing
variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]
lemma primeValuationSubring_congr {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hP : P ≠ ⊥)
    (hQ : Q ≠ ⊥) (h : P = Q) : primeValuationSubring K P hP = primeValuationSubring K Q hQ := by
  subst h
  rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open IsLocalRing
variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]
/-- Distinct nonzero primes give distinct valuation subrings. -/
lemma primeValuationSubring_injective {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hP : P ≠ ⊥)
    (hQ : Q ≠ ⊥) (he : primeValuationSubring K P hP = primeValuationSubring K Q hQ) : P = Q := by
  have h1 := placeCenter_primeValuationSubring (K := K) P hP
  have h2 := placeCenter_primeValuationSubring (K := K) Q hQ
  rw [← h1, ← h2]
  congr 1
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X])
lemma algebraMap_quadRing_apply (y : QuadRing h) :
    algebraMap (QuadRing h) (QuadField h) y = quadRingMap h y := rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X])
variable [hsq : Fact (Squarefree h)] [hirr : Fact (Irreducible (quadRat h))]
omit hsq in
/-- A valuation subring containing `ℂ[t]` contains `ℂ[t][w]`: `w² = h(t)`. -/
lemma quadRing_mem_of_polynomial_mem (O : ValuationSubring (QuadField h))
    (hO : ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField h) p ∈ O) (y : QuadRing h) :
    algebraMap (QuadRing h) (QuadField h) y ∈ O := by
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h y
  have hw : AdjoinRoot.root (quadRat h) ∈ O := by
    have hsq2 : AdjoinRoot.root (quadRat h) ^ 2 ∈ O := by
      rw [quadRoot_sq, ← IsScalarTower.algebraMap_apply]
      exact hO h
    rcases O.mem_or_inv_mem (AdjoinRoot.root (quadRat h)) with hr | hr
    · exact hr
    · by_cases h0 : AdjoinRoot.root (quadRat h) = 0
      · rw [h0]
        exact O.zero_mem
      · have he : AdjoinRoot.root (quadRat h) =
            AdjoinRoot.root (quadRat h) ^ 2 * (AdjoinRoot.root (quadRat h))⁻¹ := by
          field_simp
        rw [he]
        exact mul_mem hsq2 hr
  rw [algebraMap_quadRing_apply, quadRingMap_apply]
  exact add_mem (hO a) (mul_mem (hO b) hw)
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X])
variable [hsq : Fact (Squarefree h)] [hirr : Fact (Irreducible (quadRat h))]
theorem solution :
    (∀ (c d : ℂ) (hd : d ^ 2 = h.eval c), quadPlace h c d hd ≠ ⊤ ∧
        ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField h) p ∈ quadPlace h c d hd) ∧
      (∀ O : ValuationSubring (QuadField h), O ≠ ⊤ →
        (∀ p : ℂ[X], algebraMap ℂ[X] (QuadField h) p ∈ O) →
          ∃ (c d : ℂ) (hd : d ^ 2 = h.eval c), O = quadPlace h c d hd) ∧
      (∀ (c d c' d' : ℂ) (hd : d ^ 2 = h.eval c) (hd' : d' ^ 2 = h.eval c'),
        quadPlace h c d hd = quadPlace h c' d' hd' → c = c' ∧ d = d') := by
  refine ⟨fun c d hd => ⟨primeValuationSubring_ne_top _ _, fun p => ?_⟩, fun O htop hO => ?_,
    fun c d c' d' hd hd' he => ?_⟩
  · rw [IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]
    exact algebraMap_mem_primeValuationSubring _ _
  · have hA := quadRing_mem_of_polynomial_mem h O hO
    have hO' := eq_primeValuationSubring_placeCenter O hA htop
    have hmax : (placeCenter (QuadField h) O hA).IsMaximal :=
      (inferInstance : (placeCenter (QuadField h) O hA).IsPrime).isMaximal
        (placeCenter_ne_bot O hA htop)
    obtain ⟨c, d, hd, hP⟩ := (quadRing_isMaximal_iff h _).mp hmax
    refine ⟨c, d, hd, hO'.trans ?_⟩
    exact primeValuationSubring_congr _ _ hP
  · exact quadEval_ker_injective h hd hd' (primeValuationSubring_injective _ _ he)
end

#print axioms solution
