-- Prove2me | solution 1 for CurveSymmetry.family_holomorphicSpace_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:51.559069+00:00
-- url     : https://prove2.me/submissions/ab3e65ba-4e03-4fdf-8ef7-b013bf22674d

-- Solution generated from lean/FamilyGenus.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
import Theorems.Thm_CurveSymmetry_familyInfinityPlace_eq_comap
import Theorems.Thm_CurveSymmetry_family_place_classification
import Theorems.Thm_CurveSymmetry_mem_regularAt_familyInfinityPlace_iff
import Theorems.Thm_CurveSymmetry_mem_regularAt_quadPlace_iff
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
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma mem_holomorphicDifferentials (ω : Ω[QuadField (familyH m α)⁄ℂ]) :
    ω ∈ holomorphicDifferentials m α ↔ IsHolomorphic ω :=
  Iff.rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Point
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- A point place is a place over `ℂ` in the sense of R01a. -/
lemma quadPlace_isComplexPlace : IsComplexPlace (quadPlace h c d hd) :=
  ⟨((quad_finite_place_classification h).1 c d hd).1, quadLocal_const_mem h c d hd⟩
end Point
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityPlace_isComplexPlace : IsComplexPlace (familyInfinityPlace m α) := by
  rw [familyInfinityPlace_eq_comap]
  exact (quadPlace_isComplexPlace _ 0 0 _).comap _
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- Every place of the family's function field is a point place or the place at
infinity (`family_place_classification`, with the constants stated through `ℂ`). -/
lemma IsComplexPlace.family_cases {O : ValuationSubring (QuadField (familyH m α))}
    (hO : IsComplexPlace O) :
    (∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd) ∨
      O = familyInfinityPlace m α := by
  refine (family_place_classification (m := m) (α := α)).2 O hO.1 fun c => ?_
  rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  exact hO.2 c
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    holomorphicSpace (QuadField (familyH m α)) = holomorphicDifferentials m α := by
  ext ω
  rw [mem_holomorphicSpace, mem_holomorphicDifferentials, IsHolomorphic]
  constructor
  · intro hω
    exact ⟨fun c d hd => (mem_regularAt_quadPlace_iff _ c d hd ω).mp
        (hω _ (quadPlace_isComplexPlace _ c d hd)),
      (mem_regularAt_familyInfinityPlace_iff ω).mp (hω _ familyInfinityPlace_isComplexPlace)⟩
  · rintro ⟨hpts, hinf⟩ O hO
    rcases hO.family_cases with ⟨c, d, hd, rfl⟩ | rfl
    · exact (mem_regularAt_quadPlace_iff _ c d hd ω).mpr (hpts c d hd)
    · exact (mem_regularAt_familyInfinityPlace_iff ω).mpr hinf
end

#print axioms solution
