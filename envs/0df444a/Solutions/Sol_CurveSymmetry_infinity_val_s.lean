-- Prove2me | solution 1 for CurveSymmetry.infinity_val_s
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:34.159526+00:00
-- url     : https://prove2.me/submissions/0698fc5c-60f7-4c1a-8f03-6461af04afc2

-- Solution generated from lean/HolomorphicSpan.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Theorems.Thm_CurveSymmetry_familyInfinity_shift_sq
import Theorems.Thm_CurveSymmetry_quadLocal_poly_unit
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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- The root `w` is nonzero in the function field: `w² = h ≠ 0`. -/
lemma quadRoot_ne_zero : AdjoinRoot.root (quadRat h) ≠ 0 := by
  intro hzero
  have hsq := quadRoot_sq h
  rw [hzero, zero_pow two_ne_zero] at hsq
  have hne : algebraMap (RatFunc ℂ) (QuadField h) (algebraMap ℂ[X] (RatFunc ℂ) h) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
      (RatFunc.algebraMap_ne_zero (Fact.out : Squarefree h).ne_zero)
  exact hne hsq.symm
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Infinity
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- Membership in the conjugate local ring is valuation at most one. -/
lemma infinity_mem_iff (x : QuadField (familyH m (star α))) :
    x ∈ quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α) ↔
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation x ≤ 1 :=
  ((quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation_le_one_iff x).symm
end Infinity
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Infinity
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- A unit of the conjugate local ring has valuation one. -/
lemma infinity_val_unit {u : QuadField (familyH m (star α))}
    (hu : u ∈ quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α))
    (hu' : u⁻¹ ∈ quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α))
    (hne : u ≠ 0) :
    (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation u = 1 := by
  set v := (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
  have h1 : v u ≤ 1 := (infinity_mem_iff u).mp hu
  have h2 : v u⁻¹ ≤ 1 := (infinity_mem_iff _).mp hu'
  rw [map_inv₀] at h2
  have hpos : 0 < v u := (Valuation.pos_iff v).mpr hne
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)
end Infinity
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (quadT (familyH m (star α))) =
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (AdjoinRoot.root (quadRat (familyH m (star α)))) ^ 2 := by
  obtain ⟨k₀, hk0, hsk⟩ := familyInfinity_shift_sq (m := m) (α := α)
  obtain ⟨hkmem, hkinv⟩ := quadLocal_poly_unit _ 0 0 (familyH_star_zero_point m α) k₀ hk0
  have hk : algebraMap ℂ[X] (QuadField (familyH m (star α))) k₀ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hsk
    exact quadRoot_ne_zero _ (pow_eq_zero_iff two_ne_zero |>.mp hsk.symm)
  have hvk := infinity_val_unit hkmem hkinv hk
  have hv := congrArg (quadPlace (familyH m (star α)) 0 0
    (familyH_star_zero_point m α)).valuation hsk
  rw [map_mul, hvk, mul_one, map_pow] at hv
  exact hv
end

#print axioms solution
