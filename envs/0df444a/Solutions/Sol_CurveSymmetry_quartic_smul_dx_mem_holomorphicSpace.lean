-- Prove2me | solution 1 for CurveSymmetry.quartic_smul_dx_mem_holomorphicSpace
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:49.355567+00:00
-- url     : https://prove2.me/submissions/6d010eac-a98c-4be9-8828-611199d38f82

-- Solution generated from lean/FermatHolomorphic.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
import Theorems.Thm_CurveSymmetry_kummer_D_root
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
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
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
section Genus
variable {K : Type*} [Field K] [Algebra ℂ K]
lemma smul_D_mem_regularAt {O : ValuationSubring K} {a b : K} (ha : a ∈ O) (hb : b ∈ O) :
    a • KaehlerDifferential.D ℂ K b ∈ regularAt O :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
end Genus
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section ValuationRing
variable {K : Type*} [Field K] (O : ValuationSubring K)
/-- In a valuation subring, `aⁿ ∈ O` with `n ≠ 0` forces `a ∈ O`. -/
lemma valuationSubring_mem_of_pow_mem {a : K} {n : ℕ} (hn : n ≠ 0) (h : a ^ n ∈ O) :
    a ∈ O := by
  by_contra ha
  have hinv : a⁻¹ ∈ O := (O.mem_or_inv_mem a).resolve_left ha
  have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ O.zero_mem)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  have hk : a ^ (k + 1) * a⁻¹ ^ k = a := by
    rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, mul_one]
  exact ha (hk ▸ mul_mem h (pow_mem hinv k))
end ValuationRing
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section ValuationRing
variable {K : Type*} [Field K] (O : ValuationSubring K)
/-- For `a ∈ O`, being a unit of `O` means `a⁻¹ ∈ O`. -/
lemma valuationSubring_isUnit_iff {a : K} (ha : a ∈ O) (ha0 : a ≠ 0) :
    IsUnit (⟨a, ha⟩ : O) ↔ a⁻¹ ∈ O := by
  constructor
  · intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hab : a * (b : K) = 1 := congrArg Subtype.val hb
    rw [inv_eq_of_mul_eq_one_right hab]
    exact b.2
  · intro h
    exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ ha0),
      Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩
end ValuationRing
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quartic_polynomial_injective : Function.Injective (algebraMap ℂ[X] K₄) := by
  rw [IsScalarTower.algebraMap_eq ℂ[X] (RatFunc ℂ) K₄]
  exact (algebraMap (RatFunc ℂ) K₄).injective.comp (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticY_pow : quarticY ^ 4 = 2 - quarticX ^ 4 := by
  rw [quarticY, kummerRoot_pow]
  show algebraMap ℂ[X] K₄ (C 2 - X ^ 4) = 2 - quarticX ^ 4
  rw [map_sub, map_pow, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄,
    map_ofNat]
  rfl
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
/-- The quartic's equation `x⁴ + y⁴ = 2`. -/
lemma quartic_relation : quarticX ^ 4 + quarticY ^ 4 = 2 := by
  rw [quarticY_pow]
  ring
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticX_ne_zero : quarticX ≠ 0 := by
  intro h0
  have : algebraMap ℂ[X] K₄ X = algebraMap ℂ[X] K₄ 0 := by
    rw [map_zero]
    exact h0
  exact X_ne_zero (quartic_polynomial_injective this)
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
lemma quarticY_ne_zero : quarticY ≠ 0 := by
  intro h0
  have h := kummerRoot_pow 4 fermatQuartic
  rw [show AdjoinRoot.root (kummerRat 4 fermatQuartic) = quarticY from rfl, h0,
    zero_pow (by norm_num)] at h
  have hf : (C 2 - X ^ 4 : ℂ[X]) = 0 := quartic_polynomial_injective (by rw [map_zero]; exact h.symm)
  have := congrArg (eval 0) hf
  simp at this
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
/-- `x⁴ + y⁴ = 2` differentiates to `y³·dy = −x³·dx`. -/
lemma quartic_D_relation :
    quarticY ^ 3 • KaehlerDifferential.D ℂ K₄ quarticY =
      (-(quarticX ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticX := by
  have h := kummer_D_root 4 fermatQuartic
  have hder : algebraMap ℂ[X] K₄ (derivative fermatQuartic) = -(4 * quarticX ^ 3) := by
    show algebraMap ℂ[X] K₄ (derivative (C 2 - X ^ 4)) = -(4 * quarticX ^ 3)
    have h4C : (algebraMap ℂ[X] K₄) (C (4 : ℂ)) = 4 := by
      rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄, map_ofNat]
    rw [derivative_sub, derivative_C, zero_sub, derivative_X_pow, map_neg, map_mul, map_pow]
    simp only [Nat.cast_ofNat, h4C]
    rfl
  rw [hder, show (4 - 1 : ℕ) = 3 from rfl] at h
  have h4 : (4 : K₄) ≠ 0 := by norm_num
  calc quarticY ^ 3 • KaehlerDifferential.D ℂ K₄ quarticY
      = ((4 : K₄)⁻¹ * ((4 : ℕ) * quarticY ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticY := by
        rw [Nat.cast_ofNat, ← mul_assoc, inv_mul_cancel₀ h4, one_mul]
    _ = (4 : K₄)⁻¹ • (-(4 * quarticX ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticX := by
        rw [← smul_smul, h]
    _ = (-(quarticX ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticX := by
        rw [smul_smul]
        congr 1
        field_simp
end Quartic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section Quartic
local notation "K₄" => KummerField 4 fermatQuartic
/-- `dx = −x²·d(1/x)`. -/
lemma quartic_D_x_inv :
    KaehlerDifferential.D ℂ K₄ quarticX =
      (-(quarticX ^ 2)) • KaehlerDifferential.D ℂ K₄ quarticX⁻¹ := by
  rw [Derivation.leibniz_inv, smul_smul]
  have hx := quarticX_ne_zero
  rw [show -(quarticX ^ 2) * -(quarticX⁻¹ ^ 2) = 1 by field_simp, one_smul]
end Quartic
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
local notation "K₄" => KummerField 4 fermatQuartic
theorem solution (F : K₄)
    (h1 : ∀ O : ValuationSubring K₄,
      quarticX ∈ O → quarticY ∈ O → quarticY⁻¹ ∈ O → F ∈ O)
    (h2 : ∀ O : ValuationSubring K₄, quarticX ∈ O → quarticX⁻¹ ∈ O → quarticY ∈ O →
      F * quarticY ^ 3 * quarticX⁻¹ ^ 3 ∈ O)
    (h3 : ∀ O : ValuationSubring K₄, quarticX⁻¹ ∈ O → quarticX * quarticY⁻¹ ∈ O →
      F * quarticX ^ 2 ∈ O) :
    F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄ := by
  rw [mem_holomorphicSpace]
  intro O hO
  have hx0 := quarticX_ne_zero
  have hy0 := quarticY_ne_zero
  have htwo : (2 : K₄) ∈ O := by
    have := hO.2 2
    rwa [map_ofNat] at this
  have htwoinv : (2 : K₄)⁻¹ ∈ O := by
    have := hO.2 2⁻¹
    rwa [map_inv₀, map_ofNat] at this
  have htwo_unit : IsUnit (⟨2, htwo⟩ : O) :=
    (valuationSubring_isUnit_iff O htwo (by norm_num)).mpr htwoinv
  by_cases hx : quarticX ∈ O
  · have hy : quarticY ∈ O := valuationSubring_mem_of_pow_mem O (n := 4) (by norm_num)
      (by rw [quarticY_pow]; exact sub_mem htwo (pow_mem hx 4))
    by_cases hyi : quarticY⁻¹ ∈ O
    · exact smul_D_mem_regularAt (h1 O hx hy hyi) hx
    · -- `x` is a unit: `x⁴ + y⁴ = 2` is one and `y⁴` is not
      have hsum : (⟨quarticX, hx⟩ : O) ^ 4 + (⟨quarticY, hy⟩ : O) ^ 4 = ⟨2, htwo⟩ :=
        Subtype.ext quartic_relation
      have hxi : quarticX⁻¹ ∈ O := by
        rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hsum ▸ htwo_unit) with hX | hY
        · exact (valuationSubring_isUnit_iff O hx hx0).mp ((isUnit_pow_iff (by norm_num)).mp hX)
        · exact absurd ((valuationSubring_isUnit_iff O hy hy0).mp
            ((isUnit_pow_iff (by norm_num)).mp hY)) hyi
      have hdx : KaehlerDifferential.D ℂ K₄ quarticX =
          (-(quarticY ^ 3 * quarticX⁻¹ ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticY := by
        have hrel := congrArg (fun ω => (-(quarticX⁻¹ ^ 3)) • ω) quartic_D_relation
        simp only [smul_smul] at hrel
        rw [show -(quarticX⁻¹ ^ 3) * -(quarticX ^ 3) = 1 by field_simp, one_smul] at hrel
        rw [← hrel]
        congr 1
        ring
      rw [hdx, smul_smul]
      refine smul_D_mem_regularAt ?_ hy
      rw [show F * -(quarticY ^ 3 * quarticX⁻¹ ^ 3) = -(F * quarticY ^ 3 * quarticX⁻¹ ^ 3) by
        ring]
      exact neg_mem (h2 O hx hxi hy)
  · have hxi : quarticX⁻¹ ∈ O := (O.mem_or_inv_mem _).resolve_left hx
    have hr4 : (quarticY * quarticX⁻¹) ^ 4 = 2 * quarticX⁻¹ ^ 4 - 1 := by
      rw [mul_pow, quarticY_pow]
      field_simp
    have hr : quarticY * quarticX⁻¹ ∈ O := valuationSubring_mem_of_pow_mem O (n := 4) (by norm_num)
      (by rw [hr4]; exact sub_mem (mul_mem htwo (pow_mem hxi 4)) (one_mem O))
    have hr0 : quarticY * quarticX⁻¹ ≠ 0 := mul_ne_zero hy0 (inv_ne_zero hx0)
    -- `r = y/x` is a unit: `r⁴ − 2s⁴ = −1` and `s = 1/x` is not a unit
    have hrunit : IsUnit (⟨_, hr⟩ : O) := by
      have hsum : (⟨_, hr⟩ : O) ^ 4 + -(⟨2, htwo⟩ * (⟨quarticX⁻¹, hxi⟩ : O) ^ 4) = -1 :=
        Subtype.ext (by
          change (quarticY * quarticX⁻¹) ^ 4 + -(2 * quarticX⁻¹ ^ 4) = -1
          rw [hr4]
          ring)
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hsum ▸ isUnit_one.neg) with hR | hS
      · exact (isUnit_pow_iff (by norm_num)).mp hR
      · exfalso
        have hS4 : IsUnit ((⟨quarticX⁻¹, hxi⟩ : O) ^ 4) :=
          isUnit_of_mul_isUnit_right (IsUnit.neg_iff _ |>.mp hS)
        have := (valuationSubring_isUnit_iff O hxi (inv_ne_zero hx0)).mp
          ((isUnit_pow_iff (by norm_num)).mp hS4)
        rw [inv_inv] at this
        exact hx this
    have hrinv : quarticX * quarticY⁻¹ ∈ O := by
      have := (valuationSubring_isUnit_iff O hr hr0).mp hrunit
      rwa [mul_inv, inv_inv, mul_comm] at this
    rw [quartic_D_x_inv, smul_smul]
    refine smul_D_mem_regularAt ?_ hxi
    rw [show F * -(quarticX ^ 2) = -(F * quarticX ^ 2) by ring]
    exact neg_mem (h3 O hxi hrinv)
end

#print axioms solution
