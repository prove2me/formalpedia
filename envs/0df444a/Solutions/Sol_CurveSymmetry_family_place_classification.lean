-- Prove2me | solution 1 for CurveSymmetry.family_place_classification
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:33.986493+00:00
-- url     : https://prove2.me/submissions/86ac1eaf-8e03-4029-a7bd-422158a66196

-- Solution generated from lean/QuadraticInfinity.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Theorems.Thm_CurveSymmetry_place_eq_infinity_of_t_notMem
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
lemma familyInfinityPlace_ne_top : familyInfinityPlace m α ≠ ⊤ := by
  intro htop
  apply ((quad_finite_place_classification (familyH m (star α))).1 0 0
    (familyH_star_zero_point m α)).1
  refine top_unique fun y _ => ?_
  obtain ⟨x, rfl⟩ := familyInfinityMap_surjective (m := m) (α := α) y
  have hx : x ∈ familyInfinityPlace m α := by
    rw [htop]
    exact ValuationSubring.mem_top _
  exact (mem_familyInfinityPlace x).mp hx
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityPlace_const (c : ℂ) :
    algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ familyInfinityPlace m α := by
  rw [mem_familyInfinityPlace, familyInfinityMap_polyC]
  exact ((quad_finite_place_classification (familyH m (star α))).1 0 0
    (familyH_star_zero_point m α)).2 _
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityPlace_t_notMem :
    algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ familyInfinityPlace m α := by
  rw [mem_familyInfinityPlace, familyInfinityMap_t]
  intro hmem
  exact ((quadPlace_X_inv_mem_iff _ 0 0 (familyH_star_zero_point m α)).mp hmem) rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- A place containing the constants and `t` is a point place (G07b-2c). -/
lemma place_eq_quadPlace_of_t_mem (O : ValuationSubring (QuadField (familyH m α)))
    (htop : O ≠ ⊤) (hconst : ∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O)
    (ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∈ O) :
    ∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd := by
  apply (quad_finite_place_classification (familyH m α)).2.1 O htop
  intro p
  induction p using Polynomial.induction_on with
  | C a => exact hconst a
  | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
  | monomial n a hn =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact mul_mem hn ht
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    (familyInfinityPlace m α ≠ ⊤ ∧
        (∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ familyInfinityPlace m α) ∧
        algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ familyInfinityPlace m α) ∧
      ∀ O : ValuationSubring (QuadField (familyH m α)), O ≠ ⊤ →
        (∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O) →
          (∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd) ∨
            O = familyInfinityPlace m α := by
  refine ⟨⟨familyInfinityPlace_ne_top, familyInfinityPlace_const, familyInfinityPlace_t_notMem⟩,
    fun O htop hconst => ?_⟩
  by_cases ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∈ O
  · exact Or.inl (place_eq_quadPlace_of_t_mem O htop hconst ht)
  · exact Or.inr (place_eq_infinity_of_t_notMem O htop hconst ht)
end

#print axioms solution
