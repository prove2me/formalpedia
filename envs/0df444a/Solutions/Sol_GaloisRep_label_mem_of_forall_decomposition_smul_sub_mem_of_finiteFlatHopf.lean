-- Prove2me | solution 1 for GaloisRep.label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a3aa0edc-aa8b-5765-ba57-dd562c427106

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false
set_option linter.unusedSectionVars false

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped Pointwise

noncomputable section

namespace P2MMultO

variable (A : ValuationSubring (AlgebraicClosure ℚ))

abbrev decField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField (A.decompositionSubgroup ℚ)

def decDVR : ValuationSubring (decField A) := A.comap (algebraMap (decField A) (AlgebraicClosure ℚ))

variable {A}

theorem mem_decField_iff {x : AlgebraicClosure ℚ} :
    x ∈ decField A ↔ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → σ x = x := by
  rw [decField, IntermediateField.mem_fixedField_iff]

private def _root_.P2MMultO.val (z : decDVR A) : AlgebraicClosure ℚ := ((z : decField A) : AlgebraicClosure ℚ)

p2m_export "P2MMultO" "val"
theorem val_memA (z : decDVR A) : val z ∈ A := z.2

theorem val_fixed (z : decDVR A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    σ (val z) = val z :=
  mem_decField_iff.mp (z : decField A).2 σ hσ

private theorem _root_.P2MMultO.val_injective : Function.Injective (val (A := A)) := fun _ _ h => Subtype.ext (Subtype.ext h)

p2m_export "P2MMultO" "val_injective"
@[scoped simp] theorem val_zero : val (0 : decDVR A) = 0 := rfl
@[scoped simp] theorem val_one : val (1 : decDVR A) = 1 := rfl
@[scoped simp] theorem val_mul (x y : decDVR A) : val (x * y) = val x * val y := rfl
@[scoped simp] theorem val_add (x y : decDVR A) : val (x + y) = val x + val y := rfl
@[scoped simp] theorem val_pow (x : decDVR A) (n : ℕ) : val (x ^ n) = val x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, val_mul, ih, pow_succ]
@[scoped simp] theorem val_natCast (n : ℕ) : val ((n : decDVR A)) = n := by
  induction n with
  | zero => rfl
  | succ n ih => push_cast; rw [val_add, ih, val_one]

theorem val_ne_zero {z : decDVR A} (hz : z ≠ 0) : val z ≠ 0 := fun h => hz (val_injective (by rw [h, val_zero]))

private def _root_.P2MMultO.mkO (x : AlgebraicClosure ℚ) (hxA : x ∈ A)
    (hxD : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → σ x = x) : decDVR A :=
  ⟨⟨x, mem_decField_iff.mpr hxD⟩, hxA⟩

p2m_export "P2MMultO" "mkO"
@[scoped simp] theorem val_mkO (x : AlgebraicClosure ℚ) (hxA : x ∈ A) (hxD) : val (mkO x hxA hxD) = x := rfl

theorem isUnit_of_inv_memA {z : decDVR A} (hz : z ≠ 0) (hinv : (val z)⁻¹ ∈ A) : IsUnit z := by
  have hzF : (z : decField A) ≠ 0 := fun h => hz (Subtype.ext h)
  let w : decDVR A := ⟨(z : decField A)⁻¹, by
    show algebraMap (decField A) (AlgebraicClosure ℚ) ((z : decField A)⁻¹) ∈ A
    rw [map_inv₀]; exact hinv⟩
  refine isUnit_iff_exists_inv.mpr ⟨w, Subtype.ext ?_⟩
  show (z : decField A) * (z : decField A)⁻¹ = 1
  exact mul_inv_cancel₀ hzF

theorem valuation_val_eq_one_of_isUnit {z : decDVR A} (hz : IsUnit z) : A.valuation (val z) = 1 := by
  obtain ⟨u, rfl⟩ := hz
  have h1 : val (u : decDVR A) * val (↑u⁻¹ : decDVR A) = 1 := by rw [← val_mul, Units.mul_inv, val_one]
  have hle1 : A.valuation (val (u : decDVR A)) ≤ 1 := (A.valuation_le_one_iff _).mpr (val_memA _)
  have hle2 : A.valuation (val (↑u⁻¹ : decDVR A)) ≤ 1 := (A.valuation_le_one_iff _).mpr (val_memA _)
  have hprod : A.valuation (val (u : decDVR A)) * A.valuation (val (↑u⁻¹ : decDVR A)) = 1 := by
    rw [← map_mul, h1, map_one]
  by_contra hne
  have hlt : A.valuation (val (u : decDVR A)) < 1 := lt_of_le_of_ne hle1 hne
  have : A.valuation (val (u : decDVR A)) * A.valuation (val (↑u⁻¹ : decDVR A)) < 1 :=
    mul_lt_one_of_lt_of_le hlt hle2
  rw [hprod] at this
  exact lt_irrefl _ this

private theorem _root_.P2MMultO.not_isUnit_of_valuation_lt_one {z : decDVR A} (hz : A.valuation (val z) < 1) : ¬ IsUnit z := by
  intro hu
  rw [valuation_val_eq_one_of_isUnit hu] at hz
  exact lt_irrefl _ hz

p2m_export "P2MMultO" "not_isUnit_of_valuation_lt_one"
variable (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
include hA

omit hA in
theorem natCast_fixed (n : ℕ) : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
    σ ((n : ℕ) : AlgebraicClosure ℚ) = n := fun σ _ => map_natCast σ n

omit [Fact ℓ.Prime] in
theorem not_isUnit_ell : ¬ IsUnit ((ℓ : ℕ) : decDVR A) := by
  apply not_isUnit_of_valuation_lt_one
  rw [val_natCast]
  exact (A.mem_nonunits_iff).mp hA

theorem envelope₂ (x y : decDVR A) :
    ∃ O' : Subring (AlgebraicClosure ℚ), val x ∈ O' ∧ val y ∈ O' ∧ (O' : Set (AlgebraicClosure ℚ)) ⊆ A ∧
      IsDiscreteValuationRing O' ∧ Irreducible ((ℓ : ℕ) : O') := by
  classical
  obtain ⟨O', hS, hOA, -, hdvr, hirr, -⟩ :=
    ValuationSubring.exists_dvr_subring_of_forall_mem_decompositionSubgroup ℓ A hA {val x, val y} (by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨val_memA x, val_fixed x⟩
      · rw [Finset.mem_singleton] at ht; subst ht; exact ⟨val_memA y, val_fixed y⟩)
  refine ⟨O', hS (by simp), hS (by simp), hOA, hdvr, hirr⟩

private theorem _root_.P2MMultO.irreducible_ell : Irreducible ((ℓ : ℕ) : decDVR A) := by
  refine ⟨not_isUnit_ell ℓ hA, fun a b hab => ?_⟩
  obtain ⟨O', haO, hbO, hOA, hdvr, hirr⟩ := envelope₂ ℓ hA a b
  let a' : O' := ⟨val a, haO⟩
  let b' : O' := ⟨val b, hbO⟩
  have hab' : ((ℓ : ℕ) : O') = a' * b' := by
    apply Subtype.ext
    show ((ℓ : ℕ) : O').1 = val a * val b
    rw [← val_mul, ← hab, val_natCast]; simp
  have hne0 : ((ℓ : ℕ) : decDVR A) ≠ 0 := hirr_ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; exact hne0 (by rw [hab, zero_mul])
  have hb0 : b ≠ 0 := by rintro rfl; exact hne0 (by rw [hab, mul_zero])

  have key : ∀ (c : decDVR A) (c' : O'), c ≠ 0 → (c' : AlgebraicClosure ℚ) = val c → IsUnit c' → IsUnit c := by
    intro c c' hc0 hcc' hu
    obtain ⟨u, hu⟩ := hu
    apply isUnit_of_inv_memA hc0
    have h1 : ((u : O') : AlgebraicClosure ℚ) * ((↑u⁻¹ : O') : AlgebraicClosure ℚ) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    rw [hu, hcc'] at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact hOA (↑u⁻¹ : O').2
  rcases hirr.isUnit_or_isUnit hab' with hu | hu
  · exact Or.inl (key a a' ha0 rfl hu)
  · exact Or.inr (key b b' hb0 rfl hu)
  where
    hirr_ne_zero : ((ℓ : ℕ) : decDVR A) ≠ 0 := by
      intro h
      have := congrArg val h
      rw [val_natCast, val_zero] at this
      exact (Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast this)

p2m_export "P2MMultO" "irreducible_ell"

theorem exists_associated_pow (x : decDVR A) (hx : x ≠ 0) : ∃ n : ℕ, Associated (((ℓ : ℕ) : decDVR A) ^ n) x := by
  obtain ⟨O', hxO, -, hOA, hdvr, hirr⟩ := envelope₂ ℓ hA x x
  haveI := hdvr
  let x' : O' := ⟨val x, hxO⟩
  have hx' : x' ≠ 0 := fun h => val_ne_zero hx (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx' hirr

  have hval : val x * ((u : O') : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) ^ n := by
    have := congrArg Subtype.val hu
    simpa using this
  have huinv : ((u : O') : AlgebraicClosure ℚ) * ((↑u⁻¹ : O') : AlgebraicClosure ℚ) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  have hu0 : ((u : O') : AlgebraicClosure ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one huinv

  have hueq : ((u : O') : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) ^ n * (val x)⁻¹ := by
    rw [← hval]; field_simp [val_ne_zero hx]
  have huD : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
      σ ((u : O') : AlgebraicClosure ℚ) = ((u : O') : AlgebraicClosure ℚ) := by
    intro σ hσ
    rw [hueq, map_mul, map_pow, map_natCast, map_inv₀, val_fixed x σ hσ]
  let uO : decDVR A := mkO ((u : O') : AlgebraicClosure ℚ) (hOA (u : O').2) huD
  have huO0 : uO ≠ 0 := by
    intro h
    have := congrArg val h
    rw [val_zero] at this
    exact hu0 this
  have huOunit : IsUnit uO := by
    apply isUnit_of_inv_memA huO0
    have : (val uO)⁻¹ = ((↑u⁻¹ : O') : AlgebraicClosure ℚ) := by
      show (((u : O') : AlgebraicClosure ℚ))⁻¹ = _
      exact (eq_inv_of_mul_eq_one_right huinv).symm
    rw [this]; exact hOA (↑u⁻¹ : O').2
  obtain ⟨w, hw⟩ := huOunit
  refine ⟨n, w⁻¹, ?_⟩

  have hxu : x * uO = ((ℓ : ℕ) : decDVR A) ^ n := by
    apply val_injective
    rw [val_mul, val_mkO, hval, val_pow, val_natCast]
  rw [← hxu, ← hw, mul_assoc, Units.mul_inv, mul_one]

private theorem _root_.P2MMultO.isDiscreteValuationRing : IsDiscreteValuationRing (decDVR A) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨((ℓ : ℕ) : decDVR A), irreducible_ell ℓ hA, fun {x} hx => exists_associated_pow ℓ hA x hx⟩

p2m_export "P2MMultO" "isDiscreteValuationRing"
end P2MMultO
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO"

end
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO"

noncomputable section
namespace P2MMultOR

open P2MMultO

variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def decRing : Subring ℚ̄ := A.toSubring ⊓ (decField A).toSubring

variable {A} in
theorem mem_decRing_iff {x : ℚ̄} : x ∈ decRing A ↔ x ∈ A ∧ x ∈ decField A := by
  rw [decRing, Subring.mem_inf]
  exact Iff.rfl

def decRingEquiv : ↥(decDVR A) ≃+* ↥(decRing A) where
  toFun z := ⟨val z, mem_decRing_iff.mpr ⟨val_memA z, (z : decField A).2⟩⟩
  invFun x := ⟨⟨(x : ℚ̄), (mem_decRing_iff.mp x.2).2⟩, (ValuationSubring.mem_comap).mpr (mem_decRing_iff.mp x.2).1⟩
  left_inv z := rfl
  right_inv x := rfl
  map_mul' a b := Subtype.ext (val_mul a b)
  map_add' a b := Subtype.ext (val_add a b)

theorem coe_decRingEquiv (z : decDVR A) : ((decRingEquiv A z : decRing A) : ℚ̄) = val z := rfl

theorem decRingEquiv_symm_coe (x : decRing A) : val ((decRingEquiv A).symm x) = (x : ℚ̄) := by
  rw [← coe_decRingEquiv, RingEquiv.apply_symm_apply]

variable {A} in

def mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.decompositionSubgroup ℚ → σ x = x) : decRing A :=
  ⟨x, mem_decRing_iff.mpr ⟨hxA, mem_decField_iff.mpr hfix⟩⟩

@[scoped simp] theorem coe_mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.decompositionSubgroup ℚ → σ x = x) :
    ((mkO x hxA hfix : decRing A) : ℚ̄) = x := rfl

theorem coe_memA (x : decRing A) : (x : ℚ̄) ∈ A := (mem_decRing_iff.mp x.2).1

theorem coe_mem_decField (x : decRing A) : (x : ℚ̄) ∈ decField A := (mem_decRing_iff.mp x.2).2

theorem coe_fixed (x : decRing A) (σ : Gal) (hσ : σ ∈ A.decompositionSubgroup ℚ) : σ (x : ℚ̄) = x :=
  mem_decField_iff.mp (coe_mem_decField A x) σ hσ

private theorem _root_.P2MMultOR.mem_or_inv_mem {x : ℚ̄} (hx : x ∈ decField A) : x ∈ decRing A ∨ x⁻¹ ∈ decRing A := by
  rcases A.mem_or_inv_mem x with h | h
  · exact Or.inl (mem_decRing_iff.mpr ⟨h, hx⟩)
  · exact Or.inr (mem_decRing_iff.mpr ⟨h, IntermediateField.inv_mem _ hx⟩)

p2m_export "P2MMultOR" "mem_or_inv_mem"

private theorem _root_.P2MMultOR.not_isUnit_of_valuation_lt_one (x : decRing A) (hx : A.valuation (x : ℚ̄) < 1) : ¬ IsUnit x := by
  intro hu
  have hu' : IsUnit ((decRingEquiv A).symm x) := hu.map (decRingEquiv A).symm
  have hx' : A.valuation (val ((decRingEquiv A).symm x)) < 1 := by rwa [decRingEquiv_symm_coe]
  exact P2MMultO.not_isUnit_of_valuation_lt_one (A := A) hx' hu'

p2m_export "P2MMultOR" "not_isUnit_of_valuation_lt_one"
theorem isLocalRing (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : ℚ̄) ∈ A.nonunits) : IsLocalRing (decRing A) :=
  haveI := P2MMultO.isDiscreteValuationRing (A := A) ℓ hA
  IsLocalRing.of_surjective' (decRingEquiv A).toRingHom (decRingEquiv A).surjective

theorem isPrincipalIdealRing (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : ℚ̄) ∈ A.nonunits) :
    IsPrincipalIdealRing (decRing A) :=
  haveI := P2MMultO.isDiscreteValuationRing (A := A) ℓ hA
  IsPrincipalIdealRing.of_surjective (decRingEquiv A).toRingHom (decRingEquiv A).surjective

private theorem _root_.P2MMultOR.irreducible_ell (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : ℚ̄) ∈ A.nonunits) :
    Irreducible ((ℓ : ℕ) : decRing A) := by
  have h := P2MMultO.irreducible_ell (A := A) ℓ hA
  have : ((ℓ : ℕ) : decRing A) = decRingEquiv A ((ℓ : ℕ) : decDVR A) := by rw [map_natCast]
  rw [this]
  exact (MulEquiv.irreducible_iff (decRingEquiv A).toMulEquiv).mpr h

p2m_export "P2MMultOR" "irreducible_ell"

private theorem _root_.P2MMultOR.isDiscreteValuationRing (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : ℚ̄) ∈ A.nonunits) :
    IsDiscreteValuationRing (decRing A) := by
  haveI := isLocalRing A ℓ hA
  haveI := isPrincipalIdealRing A ℓ hA
  refine { (inferInstance : IsPrincipalIdealRing (decRing A)), (inferInstance : IsLocalRing (decRing A)) with
    not_a_field' := ?_ }
  intro hbot
  have hmem : ((ℓ : ℕ) : decRing A) ∈ IsLocalRing.maximalIdeal (decRing A) :=
    (IsLocalRing.mem_maximalIdeal _).mpr (irreducible_ell A ℓ hA).not_isUnit
  rw [hbot, Ideal.mem_bot] at hmem
  exact (irreducible_ell A ℓ hA).ne_zero hmem

p2m_export "P2MMultOR" "isDiscreteValuationRing"

scoped instance instAlgebraField : Algebra (decRing A) (decField A) :=
  (({ toFun := fun x => ⟨(x : ℚ̄), coe_mem_decField A x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl } : decRing A →+* decField A)).toAlgebra

theorem algebraMap_field_coe (x : decRing A) : ((algebraMap (decRing A) (decField A) x : decField A) : ℚ̄) = x := rfl

scoped instance instTowerField : IsScalarTower (decRing A) (decField A) ℚ̄ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance instIsFractionRing : IsFractionRing (decRing A) (decField A) where
  map_units y := by
    apply IsUnit.mk0
    intro h0
    have : ((y.1 : decRing A) : ℚ̄) = 0 := by
      have := congrArg (fun z : decField A => (z : ℚ̄)) h0
      exact this
    exact nonZeroDivisors.ne_zero y.2 (Subtype.ext this)
  surj k := by
    by_cases hk0 : (k : ℚ̄) = 0
    · refine ⟨(0, 1), ?_⟩
      have : k = 0 := Subtype.ext hk0
      rw [this]; simp
    rcases mem_or_inv_mem A k.2 with h | h
    · refine ⟨(⟨k, h⟩, 1), ?_⟩
      show k * algebraMap (decRing A) (decField A) 1 = algebraMap (decRing A) (decField A) ⟨k, h⟩
      rw [map_one, mul_one]
      exact Subtype.ext rfl
    · have hne : (⟨(k : ℚ̄)⁻¹, h⟩ : decRing A) ∈ nonZeroDivisors (decRing A) :=
        mem_nonZeroDivisors_of_ne_zero (fun h0 => hk0 (inv_eq_zero.mp (congrArg (fun z : decRing A => (z : ℚ̄)) h0)))
      refine ⟨(1, ⟨⟨(k : ℚ̄)⁻¹, h⟩, hne⟩), ?_⟩
      show k * algebraMap (decRing A) (decField A) ⟨(k : ℚ̄)⁻¹, h⟩ = algebraMap (decRing A) (decField A) 1
      rw [map_one]
      apply Subtype.ext
      show (k : ℚ̄) * (k : ℚ̄)⁻¹ = 1
      exact mul_inv_cancel₀ hk0
  exists_of_eq {a b} h := ⟨1, by
    have : ((a : ℚ̄)) = b := by
      have := congrArg (fun z : decField A => (z : ℚ̄)) h
      exact this
    rw [Subtype.ext this]⟩

end P2MMultOR
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"
end
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

set_option autoImplicit false

section P11_CLOSED

open scoped Pointwise

namespace P2MMultClosed

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem isAlgebraic_qbar : Algebra.IsAlgebraic ℚ ℚ̄ := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl

theorem isAlgClosure_qbar : IsAlgClosure ℚ ℚ̄ :=
  (isAlgClosure_iff ℚ ℚ̄).mpr ⟨inferInstance, isAlgebraic_qbar⟩

theorem normal_qbar : Normal ℚ ℚ̄ := @IsAlgClosure.normal ℚ ℚ̄ _ _ _ isAlgClosure_qbar

theorem isGalois_qbar : IsGalois ℚ ℚ̄ :=
  haveI := normal_qbar
  haveI : Algebra.IsSeparable ℚ ℚ̄ := Algebra.IsSeparable.of_integral ℚ ℚ̄
  IsGalois.mk

variable (A : ValuationSubring ℚ̄)

theorem mem_decompositionSubgroup_iff (σ : Gal) : σ ∈ A.decompositionSubgroup ℚ ↔ σ • A = A :=
  MulAction.mem_stabilizer_iff

theorem mem_decompositionSubgroup_of_forall_exists {σ : Gal}
    (h : ∀ a : ℚ̄, ∃ τ ∈ A.decompositionSubgroup ℚ, τ a = σ a) : σ ∈ A.decompositionSubgroup ℚ := by
  rw [mem_decompositionSubgroup_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hx

    obtain ⟨τ, hτD, hτ⟩ := h (σ⁻¹ • x)
    rw [mem_decompositionSubgroup_iff] at hτD
    have h1 : τ • (σ⁻¹ • x) ∈ τ • A := ValuationSubring.smul_mem_pointwise_smul τ _ A hx
    rw [hτD, AlgEquiv.smul_def, hτ, ← AlgEquiv.smul_def, smul_inv_smul] at h1
    exact h1
  · intro hx
    obtain ⟨τ, hτD, hτ⟩ := h (σ⁻¹ • x)
    have hτD' : τ⁻¹ • A = A := (mem_decompositionSubgroup_iff A _).mp (Subgroup.inv_mem _ hτD)
    have e1 : τ • (σ⁻¹ • x) = x := by rw [AlgEquiv.smul_def τ, hτ, ← AlgEquiv.smul_def, smul_inv_smul]
    have h2 : τ⁻¹ • x = σ⁻¹ • x := by
      calc τ⁻¹ • x = τ⁻¹ • (τ • (σ⁻¹ • x)) := by rw [e1]
        _ = σ⁻¹ • x := inv_smul_smul τ _
    rw [← h2, ← hτD']
    exact ValuationSubring.smul_mem_pointwise_smul τ⁻¹ _ A hx

theorem isClosed_decompositionSubgroup : IsClosed (A.decompositionSubgroup ℚ : Set Gal) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  have key : ∃ a : ℚ̄, ∀ τ ∈ A.decompositionSubgroup ℚ, τ a ≠ σ a := by
    by_contra hall
    push Not at hall
    exact hσ (mem_decompositionSubgroup_of_forall_exists A hall)
  obtain ⟨a, ha⟩ := key

  let E : IntermediateField ℚ ℚ̄ := IntermediateField.adjoin ℚ {a}
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.adjoin.finiteDimensional (isAlgebraic_qbar.isAlgebraic a).isIntegral
  refine ⟨(fun τ => σ * τ) '' (E.fixingSubgroup : Set Gal), ?_, ?_, ?_⟩
  · rintro _ ⟨τ, hτ, rfl⟩ hD
    apply ha (σ * τ) hD
    have hfix : τ • a = a := (mem_fixingSubgroup_iff _).mp hτ a (IntermediateField.mem_adjoin_simple_self ℚ a)
    rw [AlgEquiv.smul_def] at hfix
    show σ (τ a) = σ a
    rw [hfix]
  · exact (Homeomorph.mulLeft σ).isOpenMap _ (IntermediateField.fixingSubgroup_isOpen E)
  · exact ⟨1, E.fixingSubgroup.one_mem, mul_one σ⟩

theorem mem_decompositionSubgroup_of_forall_fixedField (σ : Gal)
    (hσ : ∀ x : ℚ̄, x ∈ IntermediateField.fixedField (A.decompositionSubgroup ℚ) → σ x = x) :
    σ ∈ A.decompositionSubgroup ℚ := by
  haveI := isGalois_qbar
  let D : ClosedSubgroup Gal := ⟨A.decompositionSubgroup ℚ, isClosed_decompositionSubgroup A⟩
  have h : IntermediateField.fixingSubgroup (IntermediateField.fixedField (A.decompositionSubgroup ℚ))
      = A.decompositionSubgroup ℚ :=
    InfiniteGalois.fixingSubgroup_fixedField D
  rw [← h]
  exact (mem_fixingSubgroup_iff _).mpr fun x hx => by rw [AlgEquiv.smul_def]; exact hσ x hx

end P2MMultClosed
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

end P11_CLOSED
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

section P11_SADAPT

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct
open WithConv

namespace P2MMultSAdapt

section LiftPt

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Algebra R H]

noncomputable def liftPt (φ : WithConv (H →ₐ[R] L)) : WithConv (S ⊗[R] H →ₐ[S] L) :=
  toConv (Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv fun _ _ => .all _ _)

theorem liftPt_tmul (φ : WithConv (H →ₐ[R] L)) (s : S) (h : H) :
    liftPt (S := S) φ (s ⊗ₜ[R] h) = algebraMap S L s * φ h := by
  show Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv (fun _ _ => .all _ _) (s ⊗ₜ[R] h) = _
  rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

theorem liftPt_one_tmul (φ : WithConv (H →ₐ[R] L)) (h : H) : liftPt (S := S) φ ((1 : S) ⊗ₜ[R] h) = φ h := by
  rw [liftPt_tmul, map_one, one_mul]

theorem liftPt_injective : Function.Injective (liftPt (R := R) (S := S) (L := L) (H := H)) := by
  intro φ ψ h
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  have := congrArg (fun χ : WithConv (S ⊗[R] H →ₐ[S] L) => χ ((1 : S) ⊗ₜ[R] x)) h
  simpa only [liftPt_one_tmul] using this

theorem comp_liftPt (σ : L →ₐ[S] L) (φ : WithConv (H →ₐ[R] L)) :
    σ.comp (liftPt (S := S) φ).ofConv = (liftPt (S := S) (toConv ((σ.restrictScalars R).comp φ.ofConv))).ofConv := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    rw [AlgHom.comp_apply]
    show σ (liftPt (S := S) φ (s ⊗ₜ[R] h)) = liftPt (S := S) (toConv ((σ.restrictScalars R).comp φ.ofConv)) (s ⊗ₜ[R] h)
    rw [liftPt_tmul, liftPt_tmul, map_mul, AlgHom.commutes]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end LiftPt
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

section LiftPtConv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

theorem liftPt_mul (φ ψ : WithConv (H →ₐ[R] L)) :
    liftPt (S := S) (φ * ψ) = liftPt (S := S) φ * liftPt (S := S) ψ := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  show liftPt (S := S) (φ * ψ) x = (liftPt (S := S) φ * liftPt (S := S) ψ) x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    let rr := Coalgebra.Repr.arbitrary R h
    have hco : Coalgebra.comul (R := S) (s ⊗ₜ[R] h)
        = ∑ i ∈ rr.index, ((1 : S) ⊗ₜ[R] rr.left i) ⊗ₜ[S] (s ⊗ₜ[R] rr.right i) := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← rr.eq, TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    rw [liftPt_tmul, AlgHom.convMul_apply, AlgHom.convMul_apply, ← rr.eq, map_sum, Finset.mul_sum, hco, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    show algebraMap S L s * (φ.ofConv (rr.left i) * ψ.ofConv (rr.right i))
      = liftPt (S := S) φ ((1 : S) ⊗ₜ[R] rr.left i) * liftPt (S := S) ψ (s ⊗ₜ[R] rr.right i)
    rw [liftPt_one_tmul, liftPt_tmul]
    show _ = φ.ofConv (rr.left i) * (algebraMap S L s * ψ.ofConv (rr.right i))
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftPt_one : liftPt (S := S) (1 : WithConv (H →ₐ[R] L)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  show liftPt (S := S) (1 : WithConv (H →ₐ[R] L)) x = (1 : WithConv (S ⊗[R] H →ₐ[S] L)) x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    rw [liftPt_tmul, AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftPt_pow (φ : WithConv (H →ₐ[R] L)) (n : ℕ) : liftPt (S := S) (φ ^ n) = liftPt (S := S) φ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, liftPt_one]
  | succ n ih => rw [pow_succ, pow_succ, liftPt_mul, ih]

end LiftPtConv
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

section EvGen

variable (K : Type*) (L : Type*) (B : Type*) [CommRing K] [CommRing L] [CommRing B] [Algebra K L] [Algebra K B]

noncomputable def evGen : L ⊗[K] B →ₐ[L] (WithConv (B →ₐ[K] L) → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (Pi.algHom K _ fun ν : WithConv (B →ₐ[K] L) => (WithConv.ofConv ν : B →ₐ[K] L)) (fun _ _ => Commute.all _ _)

theorem evGen_tmul (t : L) (b : B) (ν : WithConv (B →ₐ[K] L)) : evGen K L B (t ⊗ₜ[K] b) ν = t * (WithConv.ofConv ν) b := by
  simp only [evGen, Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.algHom_apply]
  rw [Algebra.ofId_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

variable {K L B}
variable {S : Type*} [CommRing S] [Algebra K S] [Algebra S L] [IsScalarTower K S L]

theorem liftPt_surjective : Function.Surjective (liftPt (R := K) (S := S) (L := L) (H := B)) := by
  intro ψ
  refine ⟨toConv (((ψ.ofConv).restrictScalars K).comp Algebra.TensorProduct.includeRight), ?_⟩
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  show liftPt (S := S) (toConv (((ψ.ofConv).restrictScalars K).comp Algebra.TensorProduct.includeRight)) x = ψ.ofConv x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s b =>
    rw [liftPt_tmul]
    show algebraMap S L s * ψ.ofConv ((1 : S) ⊗ₜ[K] b) = ψ.ofConv (s ⊗ₜ[K] b)
    rw [← ψ.ofConv.commutes s, ← map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

noncomputable def liftPtEquiv : WithConv (B →ₐ[K] L) ≃ WithConv (S ⊗[K] B →ₐ[S] L) :=
  Equiv.ofBijective (liftPt (S := S)) ⟨liftPt_injective, liftPt_surjective⟩

@[scoped simp] theorem liftPtEquiv_apply (φ : WithConv (B →ₐ[K] L)) : liftPtEquiv (S := S) φ = liftPt (S := S) φ := rfl

theorem finite_pts_baseChange [Finite (WithConv (B →ₐ[K] L))] : Finite (WithConv (S ⊗[K] B →ₐ[S] L)) :=
  Finite.of_surjective _ liftPt_surjective

theorem evGen_baseChange_apply (x : L ⊗[S] (S ⊗[K] B)) (φ : WithConv (B →ₐ[K] L)) :
    evGen S L (S ⊗[K] B) x (liftPt (S := S) φ)
      = evGen K L B (Algebra.TensorProduct.cancelBaseChange K S L L B x) φ := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul t y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero, Pi.zero_apply]
    | tmul s b =>
      rw [evGen_tmul, Algebra.TensorProduct.cancelBaseChange_tmul, evGen_tmul, Algebra.smul_def]
      show t * liftPt (S := S) φ (s ⊗ₜ[K] b) = _
      rw [liftPt_tmul]
      ring
    | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, Pi.add_apply, h₁, h₂]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem evGen_baseChange_bijective (hev : Function.Bijective (evGen K L B)) :
    Function.Bijective (evGen S L (S ⊗[K] B)) := by

  let pre : (WithConv (B →ₐ[K] L) → L) ≃ (WithConv (S ⊗[K] B →ₐ[S] L) → L) :=
    (liftPtEquiv (K := K) (L := L) (B := B) (S := S)).arrowCongr (Equiv.refl L)
  have hfac : ⇑(evGen S L (S ⊗[K] B))
      = pre ∘ evGen K L B ∘ Algebra.TensorProduct.cancelBaseChange K S L L B := by
    funext x
    funext ψ
    obtain ⟨φ, rfl⟩ := liftPt_surjective (K := K) (L := L) (S := S) ψ
    rw [evGen_baseChange_apply]
    show _ = evGen K L B _ ((liftPtEquiv (S := S)).symm (liftPtEquiv (S := S) φ))
    rw [Equiv.symm_apply_apply]
  rw [hfac]
  exact pre.bijective.comp (hev.comp (Algebra.TensorProduct.cancelBaseChange K S L L B).bijective)

end EvGen
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

section LiftPtMulEquiv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

noncomputable def liftPtMulEquiv : WithConv (H →ₐ[R] L) ≃* WithConv (S ⊗[R] H →ₐ[S] L) :=
  { liftPtEquiv (K := R) (L := L) (B := H) (S := S) with map_mul' := liftPt_mul }

@[scoped simp] theorem liftPtMulEquiv_apply (φ : WithConv (H →ₐ[R] L)) :
    liftPtMulEquiv (S := S) φ = liftPt (S := S) φ := rfl

theorem liftPtMulEquiv_symm_apply (ψ : WithConv (S ⊗[R] H →ₐ[S] L)) :
    (liftPtMulEquiv (S := S)).symm ψ = (liftPtEquiv (S := S)).symm ψ := rfl

end LiftPtMulEquiv
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

section Valuative

variable {R S L H : Type*} [CommRing R] [CommRing S] [Field L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

theorem valuation_liftPt_sub_lt_one (hS : ∀ s : S, v (algebraMap S L s) ≤ 1)
    (φ : WithConv (H →ₐ[R] L)) (hφ : ∀ h : H, v (φ h - algebraMap R L (Coalgebra.counit (R := R) h)) < 1)
    (x : S ⊗[R] H) :
    v (liftPt (S := S) φ x - algebraMap S L (Coalgebra.counit (R := S) x)) < 1 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, sub_zero, map_zero]; exact zero_lt_one
  | tmul s h =>
    rw [liftPt_tmul, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_comm (algebraMap R L _), ← mul_sub, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hS s) zero_le' (hφ h)
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    have : liftPt (S := S) φ x + liftPt (S := S) φ y - (algebraMap S L (Coalgebra.counit (R := S) x)
        + algebraMap S L (Coalgebra.counit (R := S) y))
        = (liftPt (S := S) φ x - algebraMap S L (Coalgebra.counit (R := S) x))
          + (liftPt (S := S) φ y - algebraMap S L (Coalgebra.counit (R := S) y)) := by ring
    rw [this]
    exact lt_of_le_of_lt (v.map_add _ _) (max_lt hx hy)

end Valuative
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

section Dec

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (A : ValuationSubring ℚ̄)

theorem algebraMap_O_apply (z : P2MMultOR.decRing A) : algebraMap (P2MMultOR.decRing A) ℚ̄ z = (z : ℚ̄) := rfl

theorem algebraMap_O_injective : Function.Injective (algebraMap (P2MMultOR.decRing A) ℚ̄) := Subtype.val_injective

theorem valuation_algebraMap_O_le_one (z : P2MMultOR.decRing A) : A.valuation (algebraMap (P2MMultOR.decRing A) ℚ̄ z) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (P2MMultOR.coe_memA A z)

noncomputable def galF {σ : Gal} (hσ : σ ∈ A.decompositionSubgroup ℚ) : ℚ̄ ≃ₐ[P2MMultO.decField A] ℚ̄ :=
  { σ with commutes' := fun x => P2MMultO.mem_decField_iff.mp x.2 σ hσ }

@[scoped simp] theorem galF_apply {σ : Gal} (hσ : σ ∈ A.decompositionSubgroup ℚ) (x : ℚ̄) : galF A hσ x = σ x := rfl

noncomputable def rhoD (σ : A.decompositionSubgroup ℚ) : ℚ̄ ≃ₐ[P2MMultO.decField A] ℚ̄ := galF A σ.2

@[scoped simp] theorem rhoD_apply (σ : A.decompositionSubgroup ℚ) (x : ℚ̄) : rhoD A σ x = (σ : Gal) x := rfl

theorem hfix_D (c : ℚ̄) (hc : ∀ σ : A.decompositionSubgroup ℚ, rhoD A σ c = c) :
    c ∈ Set.range (algebraMap (P2MMultO.decField A) ℚ̄) :=
  ⟨⟨c, P2MMultO.mem_decField_iff.mpr fun σ hσ => hc ⟨σ, hσ⟩⟩, rfl⟩

noncomputable def galO {σ : Gal} (hσ : σ ∈ A.decompositionSubgroup ℚ) : ℚ̄ →ₐ[P2MMultOR.decRing A] ℚ̄ :=
  { (σ : ℚ̄ →+* ℚ̄) with commutes' := fun z => P2MMultOR.coe_fixed A z σ hσ }

@[scoped simp] theorem galO_apply {σ : Gal} (hσ : σ ∈ A.decompositionSubgroup ℚ) (x : ℚ̄) : galO A hσ x = σ x := rfl

theorem galF_hn {σ : Gal} (hσ : σ ∈ A.decompositionSubgroup ℚ) {N n : ℕ}
    (hn : ∀ ζ : ℚ̄, ζ ^ N = 1 → σ ζ = ζ ^ n) : ∀ ζ : ℚ̄, ζ ^ N = 1 → galF A hσ ζ = ζ ^ n := hn

theorem galF_fix_iff {σ : Gal} (hσ : σ ∈ A.decompositionSubgroup ℚ) {X : Type*} (f : X → ℚ̄) :
    (∀ x, galF A hσ (f x) = f x) ↔ ∀ x, σ (f x) = f x := Iff.rfl

theorem galF_comp_iff {σ : Gal} (hσ : σ ∈ A.decompositionSubgroup ℚ) {X : Type*} (f g : X → ℚ̄) :
    (∀ x, g x = galF A hσ (f x)) ↔ ∀ x, g x = σ (f x) := Iff.rfl

theorem galF_restrictScalars {σ : Gal} (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    ((galF A hσ : ℚ̄ →ₐ[P2MMultO.decField A] ℚ̄).restrictScalars (P2MMultOR.decRing A)) = galO A hσ :=
  AlgHom.ext fun _ => rfl

theorem mem_D_of_forall_decRing {σ : Gal} (hσ : ∀ x ∈ P2MMultOR.decRing A, σ x = x) :
    σ ∈ A.decompositionSubgroup ℚ := by
  apply P2MMultClosed.mem_decompositionSubgroup_of_forall_fixedField
  intro x hx
  rcases P2MMultOR.mem_or_inv_mem A hx with h | h
  · exact hσ x h
  · have h1 := hσ x⁻¹ h
    rw [map_inv₀] at h1
    exact inv_injective h1

variable (q : ℕ) [Fact q.Prime]

theorem ratCast_mem_of_coprime (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) {r : ℚ} (hr : r.den.Coprime q) : (r : ℚ̄) ∈ A := by
  have hq : q.Prime := Fact.out
  have hden : A.valuation ((r.den : ℚ̄)) = 1 := by
    have hle : A.valuation ((r.den : ℚ̄)) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A r.den)
    refine le_antisymm hle (not_lt.mp fun hlt => ?_)
    have hq1 : A.valuation ((q : ℚ̄)) < 1 := (A.mem_nonunits_iff).mp hA
    have hg := Nat.gcd_eq_gcd_ab r.den q
    rw [Nat.Coprime.gcd_eq_one hr, Nat.cast_one] at hg
    have h1 : (1 : ℚ̄) = (r.den : ℚ̄) * (Nat.gcdA r.den q : ℚ̄) + (q : ℚ̄) * (Nat.gcdB r.den q : ℚ̄) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ̄)) hg
    have hlt' : A.valuation 1 < 1 := by
      rw [h1]
      refine lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hlt ((A.valuation_le_one_iff _).mpr (intCast_mem A _))
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hq1 ((A.valuation_le_one_iff _).mpr (intCast_mem A _))
    rw [map_one] at hlt'
    exact lt_irrefl _ hlt'
  have hden0 : (r.den : ℚ̄) ≠ 0 := by exact_mod_cast r.den_nz
  rw [← A.valuation_le_one_iff, Rat.cast_def, map_div₀, hden, div_one]
  exact (A.valuation_le_one_iff _).mpr (intCast_mem A r.num)

@[reducible] noncomputable def algebraRO (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) :
    Algebra (GaloisRep.ratLocalizedAt q) (P2MMultOR.decRing A) :=
  RingHom.toAlgebra
    { toFun := fun r => P2MMultOR.mkO (((r : ℚ) : ℚ̄)) (ratCast_mem_of_coprime A q hA r.2)
        (fun σ _ => by rw [← eq_ratCast (algebraMap ℚ ℚ̄), AlgEquiv.commutes])
      map_one' := Subtype.ext (by simp only [P2MMultOR.coe_mkO, Subring.coe_one]; push_cast; try rfl)
      map_mul' := fun a b => Subtype.ext (by simp only [P2MMultOR.coe_mkO, Subring.coe_mul]; push_cast; try rfl)
      map_zero' := Subtype.ext (by simp only [P2MMultOR.coe_mkO, Subring.coe_zero]; push_cast; try rfl)
      map_add' := fun a b => Subtype.ext (by simp only [P2MMultOR.coe_mkO, Subring.coe_add]; push_cast; try rfl) }

theorem algebraMap_RO_coe (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) (r : GaloisRep.ratLocalizedAt q) :
    letI := algebraRO A q hA
    ((algebraMap (GaloisRep.ratLocalizedAt q) (P2MMultOR.decRing A) r : P2MMultOR.decRing A) : ℚ̄) = ((r : ℚ) : ℚ̄) := rfl

theorem towerROQbar (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) :
    letI := algebraRO A q hA
    IsScalarTower (GaloisRep.ratLocalizedAt q) (P2MMultOR.decRing A) ℚ̄ := by
  letI := algebraRO A q hA
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rw [algebraMap_O_apply, algebraMap_RO_coe]
  show algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ r = ((r : ℚ) : ℚ̄)
  rw [IsScalarTower.algebraMap_apply (GaloisRep.ratLocalizedAt q) ℚ ℚ̄, eq_ratCast]
  rfl

end Dec
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

section T1

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (A : ValuationSubring ℚ̄)
variable {S : Type*} [CommRing S] [Bialgebra (P2MMultOR.decRing A) S] [Module.Finite (P2MMultOR.decRing A) S]

theorem apply_mem_A (ψ : S →ₐ[P2MMultOR.decRing A] ℚ̄) (s : S) : ψ s ∈ A := by
  have h1 : IsIntegral (P2MMultOR.decRing A) (ψ s) := (Algebra.IsIntegral.isIntegral s).map ψ
  obtain ⟨p, hpm, hpe⟩ := h1
  let j : P2MMultOR.decRing A →+* A :=
    { toFun := fun z => ⟨(z : ℚ̄), P2MMultOR.coe_memA A z⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  have hj : (algebraMap A ℚ̄).comp j = algebraMap (P2MMultOR.decRing A) ℚ̄ := RingHom.ext fun _ => rfl
  have h2 : IsIntegral A (ψ s) := by
    refine ⟨p.map j, hpm.map j, ?_⟩
    rw [Polynomial.eval₂_map, hj]
    exact hpe
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2

noncomputable def toQbarPt (x : WithConv (S →ₐ[P2MMultOR.decRing A] P2MMultOR.decRing A)) :
    WithConv (S →ₐ[P2MMultOR.decRing A] ℚ̄) :=
  toConv ((Algebra.ofId (P2MMultOR.decRing A) ℚ̄).comp x.ofConv)

omit [Module.Finite (P2MMultOR.decRing A) S] in
theorem toQbarPt_apply (x : WithConv (S →ₐ[P2MMultOR.decRing A] P2MMultOR.decRing A)) (s : S) :
    toQbarPt A x s = algebraMap (P2MMultOR.decRing A) ℚ̄ (x s) := rfl

omit [Module.Finite (P2MMultOR.decRing A) S] in
theorem toQbarPt_mul (x y : WithConv (S →ₐ[P2MMultOR.decRing A] P2MMultOR.decRing A)) :
    toQbarPt A (x * y) = toQbarPt A x * toQbarPt A y := by
  unfold toQbarPt
  rw [AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv]

omit [Module.Finite (P2MMultOR.decRing A) S] in
theorem toQbarPt_one : toQbarPt A (1 : WithConv (S →ₐ[P2MMultOR.decRing A] P2MMultOR.decRing A)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro s
  show algebraMap (P2MMultOR.decRing A) ℚ̄ ((1 : WithConv (S →ₐ[P2MMultOR.decRing A] P2MMultOR.decRing A)) s)
    = (1 : WithConv (S →ₐ[P2MMultOR.decRing A] ℚ̄)) s
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply]
  rfl

omit [Module.Finite (P2MMultOR.decRing A) S] in
theorem toQbarPt_pow (x : WithConv (S →ₐ[P2MMultOR.decRing A] P2MMultOR.decRing A)) (n : ℕ) :
    toQbarPt A (x ^ n) = toQbarPt A x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toQbarPt_one]
  | succ n ih => rw [pow_succ, pow_succ, toQbarPt_mul, ih]

omit [Module.Finite (P2MMultOR.decRing A) S] in
theorem toQbarPt_injective : Function.Injective (toQbarPt A (S := S)) := by
  intro x y h
  apply WithConv.ext
  apply AlgHom.ext
  intro s
  apply algebraMap_O_injective A
  rw [← toQbarPt_apply, ← toQbarPt_apply, h]

theorem exists_OPt_of_fixed [IsLocalRing (P2MMultOR.decRing A)] (ψ : WithConv (S →ₐ[P2MMultOR.decRing A] ℚ̄))
    (hfix : ∀ σ : Gal, σ ∈ A.decompositionSubgroup ℚ → ∀ s : S, σ (ψ s) = ψ s) :
    ∃ x : WithConv (S →ₐ[P2MMultOR.decRing A] P2MMultOR.decRing A),
      toQbarPt A x = ψ ∧
      (∀ s, algebraMap (P2MMultOR.decRing A) ℚ̄ (x s) = ψ s) ∧
      (∀ k : ℕ, ψ ^ k = 1 ↔ x ^ k = 1) ∧
      ((∀ s, A.valuation (ψ s - algebraMap (P2MMultOR.decRing A) ℚ̄ (Coalgebra.counit (R := P2MMultOR.decRing A) s)) < 1) →
        ∀ s, x s - algebraMap (P2MMultOR.decRing A) (P2MMultOR.decRing A) (Coalgebra.counit (R := P2MMultOR.decRing A) s)
          ∈ IsLocalRing.maximalIdeal (P2MMultOR.decRing A)) := by
  let x₀ : S → P2MMultOR.decRing A := fun s => P2MMultOR.mkO (ψ s) (apply_mem_A A ψ.ofConv s) (fun σ hσ => hfix σ hσ s)
  have hx₀ : ∀ s, ((x₀ s : P2MMultOR.decRing A) : ℚ̄) = ψ s := fun s => rfl
  let xa : S →ₐ[P2MMultOR.decRing A] P2MMultOR.decRing A :=
    { toFun := x₀
      map_one' := Subtype.ext (by rw [hx₀]; exact map_one ψ.ofConv)
      map_mul' := fun a b => Subtype.ext (by rw [hx₀, Subring.coe_mul, hx₀, hx₀]; exact map_mul ψ.ofConv a b)
      map_zero' := Subtype.ext (by rw [hx₀]; exact map_zero ψ.ofConv)
      map_add' := fun a b => Subtype.ext (by rw [hx₀, Subring.coe_add, hx₀, hx₀]; exact map_add ψ.ofConv a b)
      commutes' := fun z => Subtype.ext (by rw [hx₀]; exact ψ.ofConv.commutes z) }
  refine ⟨toConv xa, ?_, fun s => rfl, fun k => ?_, fun hred s => ?_⟩
  · exact WithConv.ext (AlgHom.ext fun s => rfl)
  · have hψ : toQbarPt A (toConv xa) = ψ := WithConv.ext (AlgHom.ext fun s => rfl)
    constructor
    · intro h
      apply toQbarPt_injective A
      rw [toQbarPt_pow, hψ, h, toQbarPt_one]
    · intro h
      rw [← hψ, ← toQbarPt_pow, h, toQbarPt_one]
  · apply (IsLocalRing.mem_maximalIdeal _).mpr
    apply P2MMultOR.not_isUnit_of_valuation_lt_one
    have hid : ∀ y : P2MMultOR.decRing A, algebraMap (P2MMultOR.decRing A) (P2MMultOR.decRing A) y = y := fun _ => rfl
    rw [hid, AddSubgroupClass.coe_sub]
    exact hred s

end T1
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR"

end P2MMultSAdapt
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSAdapt"

end P11_SADAPT
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSAdapt"

set_option autoImplicit false

section P11_SFACADE

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct
open WithConv P2MMultSAdapt

namespace P2MMultSFacade

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (q : ℕ) [Fact q.Prime]
variable (Aval : ValuationSubring ℚ̄) [Fact (((q : ℕ) : ℚ̄) ∈ Aval.nonunits)]

noncomputable scoped instance algRO : Algebra (GaloisRep.ratLocalizedAt q) (P2MMultOR.decRing Aval) :=
  algebraRO Aval q Fact.out

scoped instance towerRO : IsScalarTower (GaloisRep.ratLocalizedAt q) (P2MMultOR.decRing Aval) ℚ̄ :=
  towerROQbar Aval q Fact.out

scoped instance towerRO' : @IsScalarTower (GaloisRep.ratLocalizedAt q) (P2MMultOR.decRing Aval) ℚ̄
    Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun r =>
    @IsScalarTower.algebraMap_apply (GaloisRep.ratLocalizedAt q) (P2MMultOR.decRing Aval) ℚ̄ _ _ _ _ _ _
      (towerROQbar Aval q Fact.out) r

scoped instance towerOF' : @IsScalarTower (P2MMultOR.decRing Aval) (P2MMultO.decField Aval) ℚ̄
    Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

omit [Fact q.Prime] [Fact (((q : ℕ) : ℚ̄) ∈ Aval.nonunits)] in
scoped instance dvrO [h : Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aval.nonunits)] :
    IsDiscreteValuationRing (P2MMultOR.decRing Aval) := by
  obtain ⟨ℓ, hℓ, hA⟩ := h.out
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact P2MMultOR.isDiscreteValuationRing Aval ℓ hA

variable [Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aval.nonunits)]

example : IsPrincipalIdealRing (P2MMultOR.decRing Aval) := inferInstance
example : IsLocalRing (P2MMultOR.decRing Aval) := inferInstance

variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
  [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
  [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]

abbrev GG : Type := (P2MMultOR.decRing Aval) ⊗[GaloisRep.ratLocalizedAt q] H

abbrev PtsG : Type := WithConv (GG q Aval H →ₐ[P2MMultOR.decRing Aval] ℚ̄)

scoped instance finitePtsG [Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄))] : Finite (PtsG q Aval H) :=
  finite_pts_baseChange

variable {J : Type} [AddCommGroup J] [DistribMulAction Gal J] (M : AddSubgroup J)
variable (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) ≃ ↥M) (he_add : ∀ f g, e (f * g) = e f + e g)

noncomputable def eG : PtsG q Aval H ≃ ↥M := (liftPtEquiv (S := P2MMultOR.decRing Aval)).symm.trans e

theorem eG_liftPt (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    eG q Aval H M e (liftPt (S := P2MMultOR.decRing Aval) φ) = e φ := by
  show e ((liftPtEquiv (S := P2MMultOR.decRing Aval)).symm (liftPt _ )) = e φ
  rw [← liftPtEquiv_apply, Equiv.symm_apply_apply]

include he_add in
theorem eG_add (κ κ' : PtsG q Aval H) : eG q Aval H M e (κ * κ') = eG q Aval H M e κ + eG q Aval H M e κ' := by
  obtain ⟨φ, rfl⟩ := liftPt_surjective (K := GaloisRep.ratLocalizedAt q) (S := P2MMultOR.decRing Aval) κ
  obtain ⟨ψ, rfl⟩ := liftPt_surjective (K := GaloisRep.ratLocalizedAt q) (S := P2MMultOR.decRing Aval) κ'
  rw [← liftPt_mul, eG_liftPt, eG_liftPt, eG_liftPt, he_add]

noncomputable def lab (κ : PtsG q Aval H) : J := ((eG q Aval H M e κ : ↥M) : J)

theorem lab_liftPt (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    lab q Aval H M e (liftPt (S := P2MMultOR.decRing Aval) φ) = ((e φ : ↥M) : J) := by
  unfold lab; rw [eG_liftPt]

include he_add in
theorem lab_mul (κ κ' : PtsG q Aval H) : lab q Aval H M e (κ * κ') = lab q Aval H M e κ + lab q Aval H M e κ' := by
  unfold lab; rw [eG_add q Aval H M e he_add, AddSubgroup.coe_add]

include he_add in
theorem lab_one : lab q Aval H M e 1 = 0 := by
  have h := lab_mul q Aval H M e he_add 1 1
  erw [mul_one] at h
  exact left_eq_add.mp h

noncomputable def labHomN (N : AddSubgroup J) : PtsG q Aval H →* Multiplicative (J ⧸ N) where
  toFun κ := Multiplicative.ofAdd (QuotientAddGroup.mk (lab q Aval H M e κ) : J ⧸ N)
  map_one' := by rw [lab_one q Aval H M e he_add, QuotientAddGroup.mk_zero]; rfl
  map_mul' κ κ' := by rw [lab_mul q Aval H M e he_add, QuotientAddGroup.mk_add]; rfl

noncomputable def KN (N : AddSubgroup J) : Submonoid (PtsG q Aval H) := MonoidHom.mker (labHomN q Aval H M e he_add N)

theorem mem_KN_iff (N : AddSubgroup J) (κ : PtsG q Aval H) : κ ∈ KN q Aval H M e he_add N ↔ lab q Aval H M e κ ∈ N := by
  rw [KN, MonoidHom.mem_mker]
  show Multiplicative.ofAdd (QuotientAddGroup.mk (lab q Aval H M e κ) : J ⧸ N) = 1 ↔ _
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, QuotientAddGroup.eq_zero_iff]

variable (he_act : ∀ (σ : Gal) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)),
    (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
variable (N : AddSubgroup J) (hN : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N)

include he_act in

theorem lab_gal {σ : Gal} (hσ : σ ∈ Aval.decompositionSubgroup ℚ) (κ : PtsG q Aval H) :
    lab q Aval H M e (toConv ((galO Aval hσ).comp κ.ofConv)) = σ • lab q Aval H M e κ := by
  obtain ⟨φ, rfl⟩ := liftPt_surjective (K := GaloisRep.ratLocalizedAt q) (S := P2MMultOR.decRing Aval) κ
  have htw : toConv ((galO Aval hσ).comp (liftPt (S := P2MMultOR.decRing Aval) φ).ofConv)
      = liftPt (S := P2MMultOR.decRing Aval) (toConv (((galO Aval hσ).restrictScalars _).comp φ.ofConv)) :=
    WithConv.ext (comp_liftPt (galO Aval hσ) φ)
  rw [htw, lab_liftPt, lab_liftPt, he_act σ φ _ (fun _ => rfl)]

include he_act hN in

theorem KN_gal {σ : Gal} (hσ : σ ∈ Aval.decompositionSubgroup ℚ) {κ : PtsG q Aval H} (hκ : κ ∈ KN q Aval H M e he_add N) :
    toConv ((galO Aval hσ).comp κ.ofConv) ∈ KN q Aval H M e he_add N := by
  rw [mem_KN_iff] at hκ ⊢
  rw [lab_gal q Aval H M e he_act hσ]
  exact hN σ hσ _ hκ

include he_add he_act hN in
theorem quot_exists :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra (P2MMultOR.decRing Aval) H'),
      Module.Finite (P2MMultOR.decRing Aval) H' ∧ Module.Flat (P2MMultOR.decRing Aval) H' ∧
      Coalgebra.IsCocomm (P2MMultOR.decRing Aval) H' ∧
      ∃ (ι : H' →ₐc[P2MMultOR.decRing Aval] GG q Aval H)
        (e' : WithConv (H' →ₐ[P2MMultOR.decRing Aval] ℚ̄) ≃ ↥M ⧸ N.addSubgroupOf M),
        (∀ x y, e' (x * y) = e' x + e' y) ∧
        ∀ φ : PtsG q Aval H, e' (toConv ((ofConv φ).comp (ι : H' →ₐ[P2MMultOR.decRing Aval] GG q Aval H)))
            = QuotientAddGroup.mk (eG q Aval H M e φ) := by
  refine HopfAlgebra.exists_finiteFlat_quotient_of_forall_fixing_smul_mem (P2MMultOR.decRing Aval) (GG q Aval H) M
    (eG q Aval H M e) (eG_add q Aval H M e he_add) ?_ N ?_
  · intro σ hσO f g hfg
    have hσ : σ ∈ Aval.decompositionSubgroup ℚ := mem_D_of_forall_decRing Aval hσO
    have hg : g = toConv ((galO Aval hσ).comp f.ofConv) := WithConv.ext (AlgHom.ext fun x => hfg x)
    rw [hg]
    exact lab_gal q Aval H M e he_act hσ f
  · intro σ hσO y _ hy
    exact hN σ (mem_D_of_forall_decRing Aval hσO) y hy

def SN : Type := (quot_exists q Aval H M e he_add he_act N hN).choose

noncomputable scoped instance instCommRingSN : CommRing (SN q Aval H M e he_add he_act N hN) :=
  (quot_exists q Aval H M e he_add he_act N hN).choose_spec.choose

noncomputable scoped instance hopfSN : HopfAlgebra (P2MMultOR.decRing Aval) (SN q Aval H M e he_add he_act N hN) :=
  (quot_exists q Aval H M e he_add he_act N hN).choose_spec.choose_spec.choose

noncomputable abbrev bialgSN : Bialgebra (P2MMultOR.decRing Aval) (SN q Aval H M e he_add he_act N hN) := inferInstance

theorem SN_spec :
    Module.Finite (P2MMultOR.decRing Aval) (SN q Aval H M e he_add he_act N hN) ∧
    Module.Flat (P2MMultOR.decRing Aval) (SN q Aval H M e he_add he_act N hN) ∧
    Coalgebra.IsCocomm (P2MMultOR.decRing Aval) (SN q Aval H M e he_add he_act N hN) ∧
    ∃ (ι : SN q Aval H M e he_add he_act N hN →ₐc[P2MMultOR.decRing Aval] GG q Aval H)
      (e' : WithConv (SN q Aval H M e he_add he_act N hN →ₐ[P2MMultOR.decRing Aval] ℚ̄) ≃ ↥M ⧸ N.addSubgroupOf M),
      (∀ x y, e' (x * y) = e' x + e' y) ∧
      ∀ φ : PtsG q Aval H, e' (toConv ((ofConv φ).comp (ι : _ →ₐ[P2MMultOR.decRing Aval] GG q Aval H)))
          = QuotientAddGroup.mk (eG q Aval H M e φ) :=
  (quot_exists q Aval H M e he_add he_act N hN).choose_spec.choose_spec.choose_spec

scoped instance finiteSN : Module.Finite (P2MMultOR.decRing Aval) (SN q Aval H M e he_add he_act N hN) := (SN_spec ..).1
scoped instance flatSN : Module.Flat (P2MMultOR.decRing Aval) (SN q Aval H M e he_add he_act N hN) := (SN_spec ..).2.1
scoped instance isCocommSN' : Coalgebra.IsCocomm (P2MMultOR.decRing Aval) (SN q Aval H M e he_add he_act N hN) := (SN_spec ..).2.2.1
theorem isCocommSN : Coalgebra.IsCocomm (P2MMultOR.decRing Aval) (SN q Aval H M e he_add he_act N hN) := (SN_spec ..).2.2.1

noncomputable def ιN : SN q Aval H M e he_add he_act N hN →ₐc[P2MMultOR.decRing Aval] GG q Aval H :=
  (SN_spec q Aval H M e he_add he_act N hN).2.2.2.choose

noncomputable def eN : WithConv (SN q Aval H M e he_add he_act N hN →ₐ[P2MMultOR.decRing Aval] ℚ̄) ≃ ↥M ⧸ N.addSubgroupOf M :=
  (SN_spec q Aval H M e he_add he_act N hN).2.2.2.choose_spec.choose

theorem eN_add (x y : WithConv (SN q Aval H M e he_add he_act N hN →ₐ[P2MMultOR.decRing Aval] ℚ̄)) :
    eN q Aval H M e he_add he_act N hN (x * y) = eN q Aval H M e he_add he_act N hN x + eN q Aval H M e he_add he_act N hN y :=
  (SN_spec q Aval H M e he_add he_act N hN).2.2.2.choose_spec.choose_spec.1 x y

theorem eN_comp (φ : PtsG q Aval H) :
    eN q Aval H M e he_add he_act N hN (toConv ((ofConv φ).comp (ιN q Aval H M e he_add he_act N hN : _ →ₐ[P2MMultOR.decRing Aval] GG q Aval H)))
      = QuotientAddGroup.mk (eG q Aval H M e φ) :=
  (SN_spec q Aval H M e he_add he_act N hN).2.2.2.choose_spec.choose_spec.2 φ

noncomputable def resN (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    WithConv (SN q Aval H M e he_add he_act N hN →ₐ[P2MMultOR.decRing Aval] ℚ̄) :=
  toConv ((liftPt (S := P2MMultOR.decRing Aval) φ).ofConv.comp
    (ιN q Aval H M e he_add he_act N hN : _ →ₐ[P2MMultOR.decRing Aval] GG q Aval H))

theorem resN_apply (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) (s : SN q Aval H M e he_add he_act N hN) :
    resN q Aval H M e he_add he_act N hN φ s = liftPt (S := P2MMultOR.decRing Aval) φ (ιN q Aval H M e he_add he_act N hN s) := rfl

theorem eN_resN (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    eN q Aval H M e he_add he_act N hN (resN q Aval H M e he_add he_act N hN φ) = QuotientAddGroup.mk (e φ) := by
  rw [resN, eN_comp, eG_liftPt]

theorem resN_mul (φ ψ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    resN q Aval H M e he_add he_act N hN (φ * ψ) = resN q Aval H M e he_add he_act N hN φ * resN q Aval H M e he_add he_act N hN ψ := by
  unfold resN
  rw [liftPt_mul, AlgHom.convMul_comp_bialgHom_distrib, WithConv.toConv_ofConv]

theorem resN_one : resN q Aval H M e he_add he_act N hN 1 = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro s
  rw [resN, liftPt_one]
  show (1 : PtsG q Aval H) (ιN q Aval H M e he_add he_act N hN s)
    = (1 : WithConv (SN q Aval H M e he_add he_act N hN →ₐ[P2MMultOR.decRing Aval] ℚ̄)) s
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]

theorem resN_gal (σ : Gal) (hσ : σ ∈ Aval.decompositionSubgroup ℚ) (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    resN q Aval H M e he_add he_act N hN (toConv (((σ : ℚ̄ →ₐ[ℚ] ℚ̄).restrictScalars (GaloisRep.ratLocalizedAt q)).comp φ.ofConv))
      = toConv ((galO Aval hσ).comp (resN q Aval H M e he_add he_act N hN φ).ofConv) := by
  have hg : toConv (((σ : ℚ̄ →ₐ[ℚ] ℚ̄).restrictScalars (GaloisRep.ratLocalizedAt q)).comp φ.ofConv)
      = toConv (((galO Aval hσ).restrictScalars (GaloisRep.ratLocalizedAt q)).comp φ.ofConv) :=
    WithConv.ext (AlgHom.ext fun _ => rfl)
  rw [hg]
  apply WithConv.ext
  show (liftPt (S := P2MMultOR.decRing Aval) (toConv (((galO Aval hσ).restrictScalars _).comp φ.ofConv))).ofConv.comp _ = _
  rw [← comp_liftPt]
  rfl

theorem resN_eq_iff (φ ψ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    resN q Aval H M e he_add he_act N hN φ = resN q Aval H M e he_add he_act N hN ψ ↔ ((e φ : ↥M) : J) - ((e ψ : ↥M) : J) ∈ N := by
  rw [← (eN q Aval H M e he_add he_act N hN).injective.eq_iff, eN_resN, eN_resN, QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]

theorem resN_red (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄))
    (hφ : ∀ h : H, Aval.valuation (φ h - algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ (Coalgebra.counit h)) < 1)
    (s : SN q Aval H M e he_add he_act N hN) :
    Aval.valuation (resN q Aval H M e he_add he_act N hN φ s
      - algebraMap (P2MMultOR.decRing Aval) ℚ̄ (Coalgebra.counit (R := P2MMultOR.decRing Aval) s)) < 1 := by
  rw [resN_apply, ← CoalgHomClass.counit_comp_apply (ιN q Aval H M e he_add he_act N hN) s]
  exact valuation_liftPt_sub_lt_one Aval.valuation (valuation_algebraMap_O_le_one Aval) φ hφ _

end P2MMultSFacade
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSAdapt P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSFacade"

end P11_SFACADE
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSAdapt P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSFacade"

section P9_ELIM
namespace P2MMultFinal

open WithConv

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem elim
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (Aval : ValuationSubring ℚ̄) [Fact (((q : ℕ) : ℚ̄) ∈ Aval.nonunits)]
    [Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aval.nonunits)]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    [Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄))]
    {J : Type} [AddCommGroup J] [DistribMulAction Gal J]
    (M : AddSubgroup J) (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : Gal) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)),
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (N : AddSubgroup J) (hN : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N)
    (m : ℕ)
    (x : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄))
    (hred : ∀ h : H, Aval.valuation (x h - algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ (Coalgebra.counit h)) < 1)
    (hdisp : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ → σ • ((e x : ↥M) : J) - ((e x : ↥M) : J) ∈ N)
    (htx : x ^ (q ^ m) = 1) :
    ((e x : ↥M) : J) ∈ N := by
  classical

  letI := P2MMultSFacade.hopfSN q Aval H M e he_add he_act N hN
  haveI := P2MMultSFacade.isCocommSN q Aval H M e he_add he_act N hN
  have hA : ((q : ℕ) : ℚ̄) ∈ Aval.nonunits := Fact.out

  set ψ := P2MMultSFacade.resN q Aval H M e he_add he_act N hN x with hψdef

  have hfix : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ → ∀ s, σ (ψ s) = ψ s := by
    intro σ hσ s
    have htw : P2MMultSFacade.resN q Aval H M e he_add he_act N hN
        (toConv (((σ : ℚ̄ →ₐ[ℚ] ℚ̄).restrictScalars (GaloisRep.ratLocalizedAt q)).comp x.ofConv)) = ψ := by
      rw [hψdef, P2MMultSFacade.resN_eq_iff q Aval H M e he_add he_act N hN]
      rw [he_act σ x _ (fun _ => rfl)]
      exact hdisp σ hσ
    rw [P2MMultSFacade.resN_gal q Aval H M e he_add he_act N hN σ hσ x] at htw
    have := congrArg (fun w : WithConv (P2MMultSFacade.SN q Aval H M e he_add he_act N hN →ₐ[P2MMultOR.decRing Aval] ℚ̄) =>
      w.ofConv s) htw
    exact this

  have hψred := P2MMultSFacade.resN_red q Aval H M e he_add he_act N hN x hred

  have hψpow : ψ ^ (q ^ m) = 1 := by
    have hpow : ∀ k : ℕ, P2MMultSFacade.resN q Aval H M e he_add he_act N hN (x ^ k) = ψ ^ k := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero]; exact P2MMultSFacade.resN_one q Aval H M e he_add he_act N hN
      | succ k ih => rw [pow_succ, pow_succ, P2MMultSFacade.resN_mul q Aval H M e he_add he_act N hN, ih]
    rw [← hpow, htx]
    exact P2MMultSFacade.resN_one q Aval H M e he_add he_act N hN

  obtain ⟨x₀, hx₀ψ, -, hx₀pow, hx₀red⟩ := P2MMultSAdapt.exists_OPt_of_fixed Aval ψ hfix
  have hx₀1 : x₀ = 1 :=
    HopfAlgebra.point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
      (P2MMultOR.decRing Aval) q hq2 (P2MMultOR.irreducible_ell Aval q hA)
      (P2MMultSFacade.SN q Aval H M e he_add he_act N hN) x₀ (hx₀red hψred) m ((hx₀pow _).mp hψpow)
  have hψ1 : ψ = 1 := by rw [← hx₀ψ, hx₀1, P2MMultSAdapt.toQbarPt_one]

  have h1 : P2MMultSFacade.resN q Aval H M e he_add he_act N hN x = P2MMultSFacade.resN q Aval H M e he_add he_act N hN 1 := by
    rw [← hψdef, hψ1]; exact (P2MMultSFacade.resN_one q Aval H M e he_add he_act N hN).symm
  rw [P2MMultSFacade.resN_eq_iff q Aval H M e he_add he_act N hN] at h1
  have he1 : ((e 1 : ↥M) : J) = 0 := by
    have h := he_add 1 1
    erw [mul_one] at h
    have : (e 1 : ↥M) = 0 := left_eq_add.mp h
    rw [this]; rfl
  rwa [he1, sub_zero] at h1

end P2MMultFinal
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSAdapt P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSFacade"
end P9_ELIM
p2m_reactivate "P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultO P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultOR P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSAdapt P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.P2MMultSFacade"

set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {J : Type} [AddCommGroup J] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J) (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q)
    (m : ℕ)
    (N : AddSubgroup J)
    (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N)
    (x : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
    (hred : ∀ h : H, Aq.valuation (x h - algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1)
    (hdisp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ Aq.decompositionSubgroup ℚ →
      σ • ((e x : ↥M) : J) - ((e x : ↥M) : J) ∈ N)
    (htx : x ^ (q ^ m) = 1) :
    ((e x : ↥M) : J) ∈ N := by
  haveI : Fact (((q : ℕ) : AlgebraicClosure ℚ) ∈ Aq.nonunits) := ⟨hAq⟩
  haveI : Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ Aq.nonunits) := ⟨⟨q, Fact.out, hAq⟩⟩
  haveI : Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf q H]
    haveI : IsDiscreteValuationRing (GaloisRep.ratLocalizedAt q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
    haveI : Module.Free (GaloisRep.ratLocalizedAt q) H := Module.free_of_flat_of_isLocalRing
    haveI : Nontrivial H := by
      refine ⟨⟨1, 0, fun h10 => ?_⟩⟩
      have h1 := Bialgebra.counit_one (R := GaloisRep.ratLocalizedAt q) (A := H)
      have : (Coalgebra.counit (R := GaloisRep.ratLocalizedAt q) (A := H)) 1 = (Coalgebra.counit (R := GaloisRep.ratLocalizedAt q) (A := H)) 0 := by rw [h10]
      rw [h1, map_zero] at this
      exact one_ne_zero this
    exact Module.finrank_pos.ne'
  exact P2MMultFinal.elim q hq2 Aq H M e he_add he_act N hN m x hred hdisp htx

end S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf
end P2MW
export P2MW.S_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf (solution)
