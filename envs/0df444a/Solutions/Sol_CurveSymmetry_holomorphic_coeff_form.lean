-- Prove2me | solution 1 for CurveSymmetry.holomorphic_coeff_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:09:22.722985+00:00
-- url     : https://prove2.me/submissions/acb9798b-8e5b-47ec-a2c1-6579ebe4052b

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
import Theorems.Thm_CurveSymmetry_infinity_val_s
import Theorems.Thm_CurveSymmetry_isRegularAtInfinity_iff_cube
import Theorems.Thm_CurveSymmetry_quadLocal_poly_unit
import Theorems.Thm_CurveSymmetry_quad_ramified_uniformizer
import Theorems.Thm_CurveSymmetry_quad_regular_points_coeff
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
variable (h : ℂ[X])
lemma algebraMap_quadRing_apply (y : QuadRing h) :
    algebraMap (QuadRing h) (QuadField h) y = quadRingMap h y := rfl
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial TensorProduct
section Quad
variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]
lemma quadT_eq : quadT h = algebraMap (RatFunc ℂ) (QuadField h) RatFunc.X := by
  rw [quadT, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h), RatFunc.algebraMap_X]
end Quad
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- The image of that uniformizer in the function field is the root `w`. -/
theorem quad_ramified_uniformizer_coe :
    ((algebraMap (QuadRing h) (quadLocalRing h c d hd) (AdjoinRoot.root (quadPoly h)) :
        quadLocalRing h c d hd) : QuadField h) = AdjoinRoot.root (quadRat h) := by
  show algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.root (quadPoly h)) = _
  rw [algebraMap_quadRing_apply, quadRingMap_root]
end
end CurveSymmetry

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
section Point
variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)
/-- The root `w` lies in every point place's local ring. -/
lemma quadLocal_root_mem : AdjoinRoot.root (quadRat h) ∈ quadLocalRing h c d hd := by
  rw [← quadRingMap_root, ← algebraMap_quadRing_apply]
  exact Subalgebra.algebraMap_mem _ _
end Point
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- Polynomials in `t` embed injectively into the function field. -/
lemma algebraMap_polynomial_injective :
    Function.Injective (algebraMap ℂ[X] (QuadField (familyH m α))) := by
  rw [IsScalarTower.algebraMap_eq ℂ[X] (RatFunc ℂ) (QuadField (familyH m α))]
  exact (algebraMap (RatFunc ℂ) (QuadField (familyH m α))).injective.comp
    (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Infinity
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- The chart sends a polynomial `p(t)` to `p(1/s)`. -/
lemma familyInfinityMap_poly (p : ℂ[X]) :
    familyInfinityMap m α (algebraMap ℂ[X] (QuadField (familyH m α)) p) =
      aeval (quadT (familyH m (star α)))⁻¹ p := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m α)),
    familyInfinityMap_of, ratInv_algebraMap]
  have hcomm := Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) (QuadField (familyH m (star α))))
    (RatFunc.X : RatFunc ℂ)⁻¹ p
  rw [IsScalarTower.coe_toAlgHom', map_inv₀, ← quadT_eq] at hcomm
  exact hcomm.symm
end Infinity
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

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Infinity
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- The uniformizer `w'` has valuation strictly between `0` and `1`. -/
lemma infinity_val_root :
    0 < (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
          (AdjoinRoot.root (quadRat (familyH m (star α)))) ∧
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
          (AdjoinRoot.root (quadRat (familyH m (star α)))) < 1 := by
  set v := (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
  set O := quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
  set w := AdjoinRoot.root (quadRat (familyH m (star α)))
  have hw : w ≠ 0 := quadRoot_ne_zero _
  have hwmem : w ∈ O := quadLocal_root_mem _ 0 0 _
  refine ⟨(Valuation.pos_iff v).mpr hw, lt_of_le_of_ne ((infinity_mem_iff w).mp hwmem) ?_⟩
  intro hone
  -- then `w⁻¹` would lie in the local ring, making the uniformizer a unit
  have hinv : w⁻¹ ∈ O := by
    rw [infinity_mem_iff, map_inv₀, hone, inv_one]
  have hunit : IsUnit (⟨w, hwmem⟩ : O) :=
    (Units.mk (⟨w, hwmem⟩ : O) ⟨w⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hw))
      (Subtype.ext (inv_mul_cancel₀ hw))).isUnit
  have hmax : (⟨w, hwmem⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [quad_ramified_uniformizer _ 0 0 (familyH_star_zero_point m α)
      (familyH_eval_zero m (star α))]
    have heq : (⟨w, hwmem⟩ : O) = algebraMap (QuadRing (familyH m (star α))) O
        (AdjoinRoot.root (quadPoly (familyH m (star α)))) :=
      Subtype.ext (quad_ramified_uniformizer_coe _ 0 0 _).symm
    rw [heq]
    exact Ideal.mem_span_singleton_self _
  exact (IsLocalRing.mem_maximalIdeal _).mp hmax hunit
end Infinity
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Infinity
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- For `p ≠ 0`, `v(p(1/s)) = v(w')^(−2·deg p)`: `s^(deg p)·p(1/s)` is the reversed polynomial
evaluated at `s`, a unit because its constant term is the leading coefficient of `p`. -/
lemma infinity_val_poly (p : ℂ[X]) (hp : p ≠ 0) :
    (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (aeval (quadT (familyH m (star α)))⁻¹ p) =
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (AdjoinRoot.root (quadRat (familyH m (star α)))) ^ (-(2 * (p.natDegree : ℤ))) := by
  have hs := quadT_ne_zero (familyH m (star α))
  let : Invertible (quadT (familyH m (star α)))⁻¹ := invertibleOfNonzero (inv_ne_zero hs)
  have hrev := Polynomial.eval₂_reverse_mul_pow
    (algebraMap ℂ (QuadField (familyH m (star α)))) (quadT (familyH m (star α)))⁻¹ p
  rw [invOf_eq_inv, inv_inv, ← aeval_def, ← aeval_def] at hrev
  have hsq : aeval (quadT (familyH m (star α))) (reverse p) =
      algebraMap ℂ[X] (QuadField (familyH m (star α))) (reverse p) := by
    rw [quadT, aeval_algebraMap_apply, aeval_X_left_apply]
  have hrev0 : (reverse p).eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hp
  obtain ⟨hrmem, hrinv⟩ := quadLocal_poly_unit _ 0 0 (familyH_star_zero_point m α)
    (reverse p) hrev0
  have hrne : algebraMap ℂ[X] (QuadField (familyH m (star α))) (reverse p) ≠ 0 := by
    intro hzero
    have := algebraMap_polynomial_injective (m := m) (α := star α)
      (hzero.trans (map_zero _).symm)
    exact hp (reverse_eq_zero.mp this)
  have hvr := infinity_val_unit hrmem hrinv hrne
  rw [← hrev, hsq, map_mul, hvr, one_mul, map_pow, map_inv₀, infinity_val_s, zpow_neg,
    show (2 * (p.natDegree : ℤ)) = ((2 * p.natDegree : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, pow_mul, inv_pow]
end Infinity
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Infinity
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- Exponent bookkeeping for the `a/w` part at infinity. -/
lemma zpow_combine_even {G : Type*} [CommGroupWithZero G] {γ : G} (hγ : γ ≠ 0) (n m : ℕ) :
    γ ^ (-(2 * (n : ℤ))) * (γ * (γ ^ 2)⁻¹ ^ (m + 1))⁻¹ * (γ ^ 3)⁻¹ =
      γ ^ (2 * (m : ℤ) - 2 - 2 * n) := by
  lift γ to Gˣ using (Ne.isUnit hγ)
  simp only [← Units.val_pow_eq_pow_val, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
    ← Units.val_zpow_eq_zpow_val]
  congr 1
  group
end Infinity
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Infinity
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- Exponent bookkeeping for the `b` part at infinity. -/
lemma zpow_combine_odd {G : Type*} [CommGroupWithZero G] {γ : G} (hγ : γ ≠ 0) (n : ℕ) :
    γ ^ (-(2 * (n : ℤ))) * (γ ^ 3)⁻¹ = γ ^ (-(2 * (n : ℤ)) - 3) := by
  lift γ to Gˣ using (Ne.isUnit hγ)
  simp only [← Units.val_pow_eq_pow_val, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
    ← Units.val_zpow_eq_zpow_val]
  congr 1
  group
end Infinity
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution (f : QuadField (familyH m α))
    (hf : IsHolomorphic (f • KaehlerDifferential.D ℂ (QuadField (familyH m α))
      (quadT (familyH m α)))) :
    ∃ a : ℂ[X], a.natDegree < m ∧
      f = algebraMap ℂ[X] (QuadField (familyH m α)) a *
        (AdjoinRoot.root (quadRat (familyH m α)))⁻¹ := by
  obtain ⟨a, b, hab⟩ := quad_regular_points_coeff (familyH m α) f hf.1
  have hinf := (isRegularAtInfinity_iff_cube f).mp hf.2
  have hw : AdjoinRoot.root (quadRat (familyH m α)) ≠ 0 := quadRoot_ne_zero _
  have hfab : f = algebraMap ℂ[X] (QuadField (familyH m α)) a *
      (AdjoinRoot.root (quadRat (familyH m α)))⁻¹ + algebraMap ℂ[X] (QuadField (familyH m α)) b := by
    have : f = (f * AdjoinRoot.root (quadRat (familyH m α))) *
        (AdjoinRoot.root (quadRat (familyH m α)))⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hw, mul_one]
    rw [this, hab, add_mul, mul_assoc (algebraMap ℂ[X] _ b), mul_inv_cancel₀ hw, mul_one]
  set v := (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation with hv
  set W := AdjoinRoot.root (quadRat (familyH m (star α))) with hW
  set S := quadT (familyH m (star α)) with hS
  obtain ⟨hγpos, hγlt⟩ := infinity_val_root (m := m) (α := α)
  have hγ0 : v W ≠ 0 := ne_of_gt hγpos
  have hφw : familyInfinityMap m α (AdjoinRoot.root (quadRat (familyH m α))) =
      W * S⁻¹ ^ (m + 1) := by
    rw [familyInfinityMap_root, map_inv₀, ← quadT_eq]
  set A := aeval S⁻¹ a * (W * S⁻¹ ^ (m + 1))⁻¹ * (W ^ 3)⁻¹ with hA
  set B := aeval S⁻¹ b * (W ^ 3)⁻¹ with hB
  have hX : familyInfinityMap m α f * (W ^ 3)⁻¹ = A + B := by
    rw [hfab, map_add, map_mul, map_inv₀, familyInfinityMap_poly, familyInfinityMap_poly, hφw,
      hA, hB]
    ring
  rw [hX] at hinf
  have hvle : v (A + B) ≤ 1 := (infinity_mem_iff _).mp hinf
  have hvS : v S⁻¹ = (v W ^ 2)⁻¹ := by rw [map_inv₀, infinity_val_s]
  have hvA : a ≠ 0 → v A = v W ^ (2 * (m : ℤ) - 2 - 2 * a.natDegree) := by
    intro ha0
    rw [hA, map_mul, map_mul, map_inv₀, map_inv₀, map_mul, map_pow, map_pow, hvS,
      infinity_val_poly a ha0]
    exact zpow_combine_even hγ0 a.natDegree m
  have hvB : b ≠ 0 → v B = v W ^ (-(2 * (b.natDegree : ℤ)) - 3) := by
    intro hb0
    rw [hB, map_mul, map_inv₀, map_pow, infinity_val_poly b hb0]
    exact zpow_combine_odd hγ0 b.natDegree
  have hanti := zpow_right_strictAnti₀ hγpos hγlt
  -- the `b` part cannot survive
  have hb : b = 0 := by
    by_contra hb0
    have hBle : v B ≤ 1 := by
      by_cases ha0 : a = 0
      · have hA0 : A = 0 := by rw [hA, ha0, map_zero, zero_mul, zero_mul]
        rwa [hA0, zero_add] at hvle
      · have hne : v A ≠ v B := by
          rw [hvA ha0, hvB hb0]
          intro heq
          have := hanti.injective heq
          omega
        rw [Valuation.map_add_of_distinct_val v hne] at hvle
        exact le_trans (le_max_right _ _) hvle
    rw [hvB hb0, zpow_le_one_iff_right_of_lt_one₀ hγpos hγlt] at hBle
    omega
  refine ⟨a, ?_, by rw [hfab, hb, map_zero, add_zero]⟩
  by_cases ha0 : a = 0
  · rw [ha0, natDegree_zero]
    exact hm.out
  · have hB0 : B = 0 := by rw [hB, hb, map_zero, zero_mul]
    rw [hB0, add_zero, hvA ha0, zpow_le_one_iff_right_of_lt_one₀ hγpos hγlt] at hvle
    omega
end

#print axioms solution
