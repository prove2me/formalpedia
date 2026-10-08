-- Prove2me | solution 1 for CurveSymmetry.isRegularAtInfinity_iff_cube
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:08:17.779981+00:00
-- url     : https://prove2.me/submissions/b579152f-59f2-456a-9a01-df2c02138aa2

-- Solution generated from lean/InfinityRegularity.lean (curve-symmetry-lean): inlined helpers in
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
import Theorems.Thm_CurveSymmetry_isRegularAtInfinity_iff
import Theorems.Thm_CurveSymmetry_quadLocal_poly_unit
import Theorems.Thm_CurveSymmetry_quad_derivative_ne_zero
import Theorems.Thm_CurveSymmetry_quad_ramified_derivative_isUnit
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
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma quadT_ne_zero (h : ℂ[X]) [Fact (Irreducible (quadRat h))] : quadT h ≠ 0 := by
  rw [quadT, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h)]
  exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
    (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero)
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- Multiplying by a unit of the local ring does not change membership. -/
lemma quadLocal_mem_mul_iff {e e' x : QuadField h} (he : e ∈ quadLocalRing h c d hd)
    (he' : e' ∈ quadLocalRing h c d hd) (hee : e * e' = 1) :
    x ∈ quadLocalRing h c d hd ↔ e * x ∈ quadLocalRing h c d hd := by
  constructor
  · intro hx
    exact Subalgebra.mul_mem _ he hx
  · intro hx
    have : x = e' * (e * x) := by
      rw [← mul_assoc, mul_comm e' e, hee, one_mul]
    rw [this]
    exact Subalgebra.mul_mem _ he' hx
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- An element that becomes a unit of the local ring has its inverse there. -/
lemma quadLocal_inv_mem_of_isUnit {x : QuadRing h}
    (hx : IsUnit (algebraMap (QuadRing h) (quadLocalRing h c d hd) x)) :
    (algebraMap (QuadRing h) (QuadField h) x)⁻¹ ∈ quadLocalRing h c d hd := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hcoe : algebraMap (QuadRing h) (QuadField h) x * (y : QuadField h) = 1 := by
    have hc1 := congrArg (fun z : quadLocalRing h c d hd => (z : QuadField h)) hy
    simpa using hc1
  rw [inv_eq_of_mul_eq_one_right hcoe]
  exact y.2
end
end CurveSymmetry

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

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution (f : QuadField (familyH m α)) :
    IsRegularAtInfinity (f • KaehlerDifferential.D ℂ (QuadField (familyH m α))
        (quadT (familyH m α))) ↔
      familyInfinityMap m α f * (AdjoinRoot.root (quadRat (familyH m (star α))) ^ 3)⁻¹ ∈
        quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α) := by
  set h' := familyH m (star α) with hh'
  set O := quadLocalRing h' 0 0 (familyH_star_zero_point m α)
  set s := quadT h'
  set w := AdjoinRoot.root (quadRat h')
  set hp := algebraMap ℂ[X] (QuadField h') h'.derivative
  obtain ⟨k₀, hk0, hsk⟩ := familyInfinity_shift_sq (m := m) (α := α)
  set k := algebraMap ℂ[X] (QuadField h') k₀
  have hc0 := familyH_eval_zero m (star α)
  have hw : w ≠ 0 := quadRoot_ne_zero h'
  have hs : s ≠ 0 := quadT_ne_zero h'
  have hk : k ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hsk
    exact hw (pow_eq_zero_iff two_ne_zero |>.mp hsk.symm)
  have hpne : hp ≠ 0 := quad_derivative_ne_zero h' 0 hc0
  obtain ⟨hkmem, hkinv⟩ := quadLocal_poly_unit h' 0 0 (familyH_star_zero_point m α) k₀ hk0
  have hpmem : hp ∈ O := by
    have : hp = algebraMap (QuadRing h') (QuadField h')
        (algebraMap ℂ[X] (QuadRing h') h'.derivative) := by
      rw [← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h') (QuadField h')]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  have hpinv : hp⁻¹ ∈ O := by
    have : hp = algebraMap (QuadRing h') (QuadField h')
        (algebraMap ℂ[X] (QuadRing h') h'.derivative) := by
      rw [← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h') (QuadField h')]
    rw [this]
    exact quadLocal_inv_mem_of_isUnit h' 0 0 (familyH_star_zero_point m α)
      (quad_ramified_derivative_isUnit h' 0 0 (familyH_star_zero_point m α) hc0)
  have htwo : (2 : QuadField h') ∈ O := by
    rw [show (2 : QuadField h') = algebraMap ℂ (QuadField h') 2 from
      (map_ofNat (algebraMap ℂ (QuadField h')) 2).symm]
    exact quadLocal_const_mem h' 0 0 (familyH_star_zero_point m α) 2
  have htwoinv : (2 : QuadField h')⁻¹ ∈ O := by
    rw [show (2 : QuadField h')⁻¹ = algebraMap ℂ (QuadField h') 2⁻¹ by
      rw [map_inv₀, map_ofNat]]
    exact quadLocal_const_mem h' 0 0 (familyH_star_zero_point m α) _
  -- the unit relating the raw coefficient to `φ(f)/w'³`
  set e := -(2 * k ^ 2) * hp⁻¹ with he
  set e' := -(hp * k⁻¹ ^ 2 * 2⁻¹) with he'
  have hemem : e ∈ O :=
    Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (Subalgebra.mul_mem _ htwo
      (Subalgebra.pow_mem _ hkmem 2))) hpinv
  have he'mem : e' ∈ O :=
    Subalgebra.neg_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hpmem
      (Subalgebra.pow_mem _ hkinv 2)) htwoinv)
  have hee : e * e' = 1 := by
    rw [he, he']
    calc -(2 * k ^ 2) * hp⁻¹ * -(hp * k⁻¹ ^ 2 * 2⁻¹)
        = (2 * 2⁻¹) * (k * k⁻¹) ^ 2 * (hp⁻¹ * hp) := by ring
      _ = 1 := by
        rw [mul_inv_cancel₀ two_ne_zero, mul_inv_cancel₀ hk, inv_mul_cancel₀ hpne]
        ring
  have hsval : s = w ^ 2 * k⁻¹ := by
    rw [← hsk, mul_assoc, mul_inv_cancel₀ hk, mul_one]
  have hraw : familyInfinityMap m α f * ((s ^ 2 * hp)⁻¹ * -(2 * w)) =
      e * (familyInfinityMap m α f * (w ^ 3)⁻¹) := by
    rw [hsval, he]
    field_simp
  rw [isRegularAtInfinity_iff, hraw]
  exact (quadLocal_mem_mul_iff h' 0 0 (familyH_star_zero_point m α) hemem he'mem hee).symm
end

#print axioms solution
