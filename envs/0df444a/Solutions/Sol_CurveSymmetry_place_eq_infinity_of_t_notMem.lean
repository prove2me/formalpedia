-- Prove2me | solution 1 for CurveSymmetry.place_eq_infinity_of_t_notMem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:54.793976+00:00
-- url     : https://prove2.me/submissions/67db93e8-712d-46fb-810e-13e04be2e40f

-- Solution generated from lean/QuadraticInfinity.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Theorems.Thm_CurveSymmetry_quadPlace_X_inv_mem_iff
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

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityMap_t :
    familyInfinityMap m α (algebraMap ℂ[X] (QuadField (familyH m α)) X) =
      (algebraMap ℂ[X] (QuadField (familyH m (star α))) X)⁻¹ := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m α)),
    familyInfinityMap_of, RatFunc.algebraMap_X, ratInv_X, map_inv₀,
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m (star α))),
    RatFunc.algebraMap_X]
end CurveSymmetry

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
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityEquiv_symm_apply {x : QuadField (familyH m α)}
    {y : QuadField (familyH m (star α))} (hxy : familyInfinityMap m α x = y) :
    (familyInfinityEquiv m α).symm y = x := by
  rw [← hxy]
  exact (familyInfinityEquiv m α).symm_apply_apply x
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution (O : ValuationSubring (QuadField (familyH m α)))
    (htop : O ≠ ⊤) (hconst : ∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O)
    (ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ O) :
    O = familyInfinityPlace m α := by
  let e := familyInfinityEquiv m α
  let Q := O.comap e.symm.toRingHom
  have hQmem (y : QuadField (familyH m (star α))) : y ∈ Q ↔ e.symm y ∈ O := Iff.rfl
  have hQtop : Q ≠ ⊤ := by
    intro hQ
    apply htop
    refine top_unique fun x _ => ?_
    have hx : e x ∈ Q := by
      rw [hQ]
      exact ValuationSubring.mem_top _
    rwa [hQmem, RingEquiv.symm_apply_apply] at hx
  have htinv : (algebraMap ℂ[X] (QuadField (familyH m α)) X)⁻¹ ∈ O :=
    (O.mem_or_inv_mem _).resolve_left ht
  have hsX : e.symm (algebraMap ℂ[X] (QuadField (familyH m (star α))) X) =
      (algebraMap ℂ[X] (QuadField (familyH m α)) X)⁻¹ := by
    apply familyInfinityEquiv_symm_apply
    rw [map_inv₀, familyInfinityMap_t, inv_inv]
  have hsXinv : e.symm (algebraMap ℂ[X] (QuadField (familyH m (star α))) X)⁻¹ =
      algebraMap ℂ[X] (QuadField (familyH m α)) X :=
    familyInfinityEquiv_symm_apply familyInfinityMap_t
  have hQpoly : ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField (familyH m (star α))) p ∈ Q := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
        rw [hQmem, familyInfinityEquiv_symm_apply (familyInfinityMap_polyC a)]
        exact hconst a
    | add p q hp hq =>
        rw [map_add]
        exact add_mem hp hq
    | monomial n a hn =>
        rw [pow_succ, ← mul_assoc, map_mul]
        refine mul_mem hn ?_
        rw [hQmem, hsX]
        exact htinv
  obtain ⟨c, d, hd, hQ⟩ :=
    (quad_finite_place_classification (familyH m (star α))).2.1 Q hQtop hQpoly
  have hc : c = 0 := by
    by_contra hc
    have hin := (quadPlace_X_inv_mem_iff _ c d hd).mpr hc
    rw [← hQ, hQmem, hsXinv] at hin
    exact ht hin
  subst hc
  have hd0 : d = 0 := by
    rw [familyH_eval_zero] at hd
    exact (pow_eq_zero_iff two_ne_zero).mp hd
  subst hd0
  ext x
  rw [mem_familyInfinityPlace]
  change x ∈ O ↔ e x ∈ quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
  rw [← hQ, hQmem, RingEquiv.symm_apply_apply]
end

#print axioms solution
