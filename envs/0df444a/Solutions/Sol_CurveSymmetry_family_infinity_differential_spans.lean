-- Prove2me | solution 1 for CurveSymmetry.family_infinity_differential_spans
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:52.909338+00:00
-- url     : https://prove2.me/submissions/a386052d-0b50-4864-8615-10c1a521b31f

-- Solution generated from lean/InfinityDifferentials.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
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
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma mem_familyInfinityPlace (x : QuadField (familyH m α)) :
    x ∈ familyInfinityPlace m α ↔
      familyInfinityMap m α x ∈ quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α) :=
  Iff.rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
section Transport
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
/-- A generator of the differentials transports along an isomorphism of `R`-algebras. -/
theorem kaehler_span_D_equiv (e : A ≃ₐ[R] B) {a : A}
    (ha : Submodule.span A {KaehlerDifferential.D R A a} = ⊤) :
    Submodule.span B {KaehlerDifferential.D R B (e a)} = ⊤ := by
  let : Algebra A B := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  have : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ => rfl)
  have hspan := kaehler_span_map_eq_top R A B ha
  rwa [KaehlerDifferential.map_D] at hspan
end Transport
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- The conjugate family's point place `(0, 0)` is the one that the place at infinity
pulls back from. -/
lemma mem_familyInfinityPlace_iff_symm (y : quadLocalRing (familyH m (star α)) 0 0
    (familyH_star_zero_point m α)) :
    (familyInfinityAlgEquiv m α).symm (y : QuadField (familyH m (star α))) ∈
      familyInfinityPlace m α := by
  rw [mem_familyInfinityPlace]
  show familyInfinityAlgEquiv m α ((familyInfinityAlgEquiv m α).symm _) ∈ _
  rw [AlgEquiv.apply_symm_apply]
  exact y.2
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    ∃ x : QuadField (familyH m α),
      x ∈ familyInfinityPlace m α ∧
        (∃ u : quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α),
          IsLocalRing.maximalIdeal
              (quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α)) =
            Ideal.span {u} ∧ familyInfinityMap m α x = (u : QuadField (familyH m (star α)))) ∧
        Submodule.span (QuadField (familyH m α))
            {KaehlerDifferential.D ℂ (QuadField (familyH m α)) x} = ⊤ ∧
          KaehlerDifferential.D ℂ (QuadField (familyH m α)) x ≠ 0 := by
  obtain ⟨u, hu, -⟩ :=
    quadLocal_exists_uniformizer (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
  refine ⟨(familyInfinityAlgEquiv m α).symm (u : QuadField (familyH m (star α))),
    mem_familyInfinityPlace_iff_symm u, ⟨u, hu, ?_⟩, ?_, ?_⟩
  · show familyInfinityAlgEquiv m α ((familyInfinityAlgEquiv m α).symm _) = _
    rw [AlgEquiv.apply_symm_apply]
  · exact kaehler_span_D_equiv (familyInfinityAlgEquiv m α).symm
      (quadLocal_D_uniformizer_spans (familyH m (star α)) 0 0 (familyH_star_zero_point m α) hu)
  · exact quad_D_ne_zero_of_span (familyH m α)
      (kaehler_span_D_equiv (familyInfinityAlgEquiv m α).symm
        (quadLocal_D_uniformizer_spans (familyH m (star α)) 0 0
          (familyH_star_zero_point m α) hu))
end

#print axioms solution
