-- Prove2me | solution 1 for GaloisRep.multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c9b05ffa-a4ef-59dd-99aa-4c9e04fca113

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_SchematicClosure
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_FiniteFlat_ClosureHopfAlgebra
import Definitions.Def_HopfAlgebra_CharacterClosure
import Theorems.Thm_HopfAlgebra_characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable
import Theorems.Thm_HopfAlgebra_exists_characterClosure_points_equiv
import Theorems.Thm_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq
import Theorems.Thm_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf
import Theorems.Thm_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_quotient_of_forall_fixing_smul_mem
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO"

end
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO"

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"
end
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

set_option autoImplicit false

section P11_CLOSED

open scoped Pointwise

namespace P2MMultClosed

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem isAlgebraic_qbar : Algebra.IsAlgebraic ℚ ℚ̄ := by
  convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

end P11_CLOSED
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR"

end P2MMultSAdapt
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt"

end P11_SADAPT
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt"

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
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade"

end P11_SFACADE
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade"

section P11_SFACADE_G4

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct
open WithConv P2MMultSAdapt

namespace P2MMultSFacade

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (q : ℕ) [Fact q.Prime]
variable (Aval : ValuationSubring ℚ̄) [Fact (((q : ℕ) : ℚ̄) ∈ Aval.nonunits)]
variable [Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aval.nonunits)]
variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
  [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
  [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
variable {J : Type} [AddCommGroup J] [DistribMulAction Gal J] (M : AddSubgroup J)
variable (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) ≃ ↥M) (he_add : ∀ f g, e (f * g) = e f + e g)
variable (he_act : ∀ (σ : Gal) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)),
    (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
variable (N : AddSubgroup J) (hN : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N)

set_option maxSynthPendingDepth 3

abbrev PtsF : Type := WithConv ((P2MMultO.decField Aval) ⊗[P2MMultOR.decRing Aval] GG q Aval H →ₐ[P2MMultO.decField Aval] ℚ̄)

scoped instance finitePtsF [Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄))] : Finite (PtsF q Aval H) :=
  finite_pts_baseChange (K := P2MMultOR.decRing Aval) (S := P2MMultO.decField Aval) (B := GG q Aval H)

omit [Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aval.nonunits)] [Module.Finite (GaloisRep.ratLocalizedAt q) H]
  [Module.Flat (GaloisRep.ratLocalizedAt q) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H] in

theorem evGen_bijective_PtsF (hev : Function.Bijective (evGen (GaloisRep.ratLocalizedAt q) ℚ̄ H)) :
    Function.Bijective (evGen (P2MMultO.decField Aval) ℚ̄ ((P2MMultO.decField Aval) ⊗[P2MMultOR.decRing Aval] GG q Aval H)) :=
  evGen_baseChange_bijective (K := P2MMultOR.decRing Aval) (S := P2MMultO.decField Aval)
    (evGen_baseChange_bijective (K := GaloisRep.ratLocalizedAt q) (S := P2MMultOR.decRing Aval) hev)

noncomputable def KNF : Submonoid (PtsF q Aval H) :=
  (KN q Aval H M e he_add N).map
    (liftPtMulEquiv (R := P2MMultOR.decRing Aval) (S := P2MMultO.decField Aval) (L := ℚ̄) (H := GG q Aval H)).toMonoidHom

theorem mem_KNF_iff (ν : PtsF q Aval H) :
    ν ∈ KNF q Aval H M e he_add N ↔ (liftPtEquiv (S := P2MMultO.decField Aval)).symm ν ∈ KN q Aval H M e he_add N := by
  rw [KNF, Submonoid.mem_map]
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, liftPtMulEquiv_apply, ← liftPtEquiv_apply, Equiv.symm_apply_apply]
    exact hκ
  · intro h
    exact ⟨_, h, by rw [MulEquiv.coe_toMonoidHom, liftPtMulEquiv_apply, ← liftPtEquiv_apply, Equiv.apply_symm_apply]⟩

theorem liftPt_mem_KNF_iff (κ : PtsG q Aval H) :
    liftPt (S := P2MMultO.decField Aval) κ ∈ KNF q Aval H M e he_add N ↔ κ ∈ KN q Aval H M e he_add N := by
  rw [mem_KNF_iff, ← liftPtEquiv_apply, Equiv.symm_apply_apply]

theorem mem_KNF_iff_lab (ν : PtsF q Aval H) :
    ν ∈ KNF q Aval H M e he_add N ↔ lab q Aval H M e ((liftPtEquiv (S := P2MMultO.decField Aval)).symm ν) ∈ N := by
  rw [mem_KNF_iff, mem_KN_iff]

noncomputable def antipodeAlgHomG : GG q Aval H →ₐ[P2MMultOR.decRing Aval] GG q Aval H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode (P2MMultOR.decRing Aval)) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

@[scoped simp] theorem antipodeAlgHomG_apply (g : GG q Aval H) :
    antipodeAlgHomG q Aval H g = HopfAlgebra.antipode (P2MMultOR.decRing Aval) g := rfl

theorem comp_antipode_mul (κ : PtsG q Aval H) : toConv (κ.ofConv.comp (antipodeAlgHomG q Aval H)) * κ = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro g
  have hl : (toConv (κ.ofConv.comp (antipodeAlgHomG q Aval H)) * κ) g
      = Algebra.TensorProduct.lift (toConv (κ.ofConv.comp (antipodeAlgHomG q Aval H))).ofConv κ.ofConv
          (fun _ _ => .all _ _) (Coalgebra.comul g) := AlgHom.convMul_apply _ _ _
  have hr : (1 : PtsG q Aval H) g = algebraMap (P2MMultOR.decRing Aval) ℚ̄ (Coalgebra.counit g) := AlgHom.convOne_apply _
  rw [hl, hr]
  let rr := Coalgebra.Repr.arbitrary (P2MMultOR.decRing Aval) g
  conv_lhs => rw [← rr.eq]
  simp only [map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Function.comp_apply, antipodeAlgHomG_apply]
  rw [← κ.ofConv.commutes, ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit rr, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]

include he_add in
theorem comp_antipode_mem_KN {κ : PtsG q Aval H} (hκ : κ ∈ KN q Aval H M e he_add N) :
    toConv (κ.ofConv.comp (antipodeAlgHomG q Aval H)) ∈ KN q Aval H M e he_add N := by
  rw [mem_KN_iff] at hκ ⊢
  have h := lab_mul q Aval H M e he_add (toConv (κ.ofConv.comp (antipodeAlgHomG q Aval H))) κ
  rw [comp_antipode_mul, lab_one q Aval H M e he_add] at h
  have h' : lab q Aval H M e (toConv (κ.ofConv.comp (antipodeAlgHomG q Aval H))) = - lab q Aval H M e κ :=
    eq_neg_of_add_eq_zero_left h.symm
  rw [h']
  exact N.neg_mem hκ

set_option maxHeartbeats 6400000 in

theorem KNF_inv (ν : (P2MMultO.decField Aval) ⊗[P2MMultOR.decRing Aval] GG q Aval H →ₐ[P2MMultO.decField Aval] ℚ̄)
    (hν : toConv ν ∈ KNF q Aval H M e he_add N) :
    ∃ ν' : (P2MMultO.decField Aval) ⊗[P2MMultOR.decRing Aval] GG q Aval H →ₐ[P2MMultO.decField Aval] ℚ̄,
      toConv ν' ∈ KNF q Aval H M e he_add N ∧
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := P2MMultO.decField Aval) := by
  obtain ⟨κ, hκ⟩ := liftPt_surjective (K := P2MMultOR.decRing Aval) (S := P2MMultO.decField Aval) (toConv ν)
  have hκN : κ ∈ KN q Aval H M e he_add N := by rw [← liftPt_mem_KNF_iff, hκ]; exact hν
  refine ⟨(liftPt (S := P2MMultO.decField Aval) (toConv (κ.ofConv.comp (antipodeAlgHomG q Aval H)))).ofConv, ?_, ?_⟩
  · rw [WithConv.toConv_ofConv, liftPt_mem_KNF_iff]
    exact comp_antipode_mem_KN q Aval H M e he_add N hκN
  · have hν' : ∀ x, ν x = liftPt (S := P2MMultO.decField Aval) κ x := fun x =>
      (DFunLike.congr_fun (congrArg WithConv.ofConv hκ) x).symm
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, hν']
    show liftPt (S := P2MMultO.decField Aval) (toConv (κ.ofConv.comp (antipodeAlgHomG q Aval H))) x
      = liftPt (S := P2MMultO.decField Aval) κ (HopfAlgebraStruct.antipode _ x)
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul f g =>
      have hS : HopfAlgebraStruct.antipode (R := P2MMultO.decField Aval) (f ⊗ₜ[P2MMultOR.decRing Aval] g)
          = f ⊗ₜ[P2MMultOR.decRing Aval] HopfAlgebraStruct.antipode (R := P2MMultOR.decRing Aval) g := rfl
      rw [hS, liftPt_tmul, liftPt_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

include he_act hN in

theorem KNF_stab {σ : Gal} (hσ : σ ∈ Aval.decompositionSubgroup ℚ)
    (τ : ℚ̄ →ₐ[P2MMultO.decField Aval] ℚ̄) (hτ : ∀ x, τ x = σ x)
    {ν : PtsF q Aval H} (hν : ν ∈ KNF q Aval H M e he_add N) :
    toConv (τ.comp ν.ofConv) ∈ KNF q Aval H M e he_add N := by
  obtain ⟨κ, rfl⟩ := liftPt_surjective (K := P2MMultOR.decRing Aval) (S := P2MMultO.decField Aval) ν
  rw [liftPt_mem_KNF_iff] at hν
  have h1 : toConv (τ.comp (liftPt (S := P2MMultO.decField Aval) κ).ofConv)
      = liftPt (S := P2MMultO.decField Aval) (toConv ((τ.restrictScalars (P2MMultOR.decRing Aval)).comp κ.ofConv)) :=
    WithConv.ext (comp_liftPt τ κ)
  have h2 : toConv ((τ.restrictScalars (P2MMultOR.decRing Aval)).comp κ.ofConv) = toConv ((galO Aval hσ).comp κ.ofConv) :=
    WithConv.ext (AlgHom.ext fun x => hτ (κ.ofConv x))
  rw [h1, liftPt_mem_KNF_iff, h2]
  exact KN_gal q Aval H M e he_add he_act N hN hσ hν

end P2MMultSFacade
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade"

end P11_SFACADE_G4
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace P2MMultE

open scoped TensorProduct

private theorem _root_.P2MMultE.toConv_ofConv {X : Type*} (x : WithConv X) : WithConv.toConv x.ofConv = x := rfl

p2m_export "P2MMultE" "toConv_ofConv"
section ConvBridge

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [Bialgebra R H]
variable {C : Type*} [CommRing C] [Algebra R C]

theorem brConv_mul_apply (x y : WithConv (H →ₐ[R] C)) (a : H) :
    (x * y).ofConv a = Algebra.TensorProduct.lmul' R (S := C)
      (Algebra.TensorProduct.map x.ofConv y.ofConv (Coalgebra.comul (R := R) a)) := rfl

theorem brConv_one_apply (a : H) :
    (1 : WithConv (H →ₐ[R] C)).ofConv a = algebraMap R C (Coalgebra.counit (R := R) a) := rfl

theorem conv_mul_comm_of_isCocomm [Coalgebra.IsCocomm R H] (x y : WithConv (H →ₐ[R] C)) : x * y = y * x := by
  rw [← toConv_ofConv (x * y), ← toConv_ofConv (y * x)]
  congr 1
  apply AlgHom.ext
  intro a
  rw [brConv_mul_apply, brConv_mul_apply]
  conv_rhs => rw [← Coalgebra.comm_comul R a]
  induction (Coalgebra.comul (R := R) a) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a₁ a₂ =>
    rw [TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem submonoid_mul_comm_of_isCocomm [Coalgebra.IsCocomm R H] (S : Submonoid (WithConv (H →ₐ[R] C)))
    (μ μ' : ↥S) : μ * μ' = μ' * μ :=
  Subtype.ext (conv_mul_comm_of_isCocomm (μ : WithConv (H →ₐ[R] C)) μ')

end ConvBridge
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade"

section Facade

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]
variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]
variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

private abbrev _root_.P2MMultE.ptSet (S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))) : Set (F ⊗[O] A →ₐ[F] L) := HopfAlgebra.ptSet S
p2m_export "P2MMultE" "ptSet"
noncomputable abbrev evQ (S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))) := HopfAlgebra.evalQuot S

structure IPtHyp (S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))) : Prop where
  sep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
    (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
      HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0
  inv_mem : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
    ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)

theorem IPtHyp.of_sep_inv
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) : IPtHyp S :=
  ⟨hsep, hinv⟩

noncomputable abbrev ES (h : IPtHyp S) : Subalgebra O (CartierDual O A) :=
  HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)

theorem T4facts (h : IPtHyp S) :
    ((HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S) : Set (F ⊗[O] CartierDual O A))
        = {w | ∀ x ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S),
            CartierDual.dualBaseChangeLin O F A w x = 0}) ∧
    IsComulStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) ∧
    IsAntipodeStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) :=
  HopfAlgebra.characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable O F A L S h.sep h.inv_mem

@[reducible] noncomputable def hopfES (h : IPtHyp S) : HopfAlgebra O ↥(ES h) :=
  closureHopfAlgebra O F (T4facts h).2.1 (T4facts h).2.2

theorem isCocommES (h : IPtHyp S) :
    letI := hopfES h
    Coalgebra.IsCocomm O ↥(ES h) :=
  closureIsCocomm (T4facts h).2.1

scoped instance instModuleFiniteES (h : IPtHyp S) : Module.Finite O ↥(ES h) := flatClosure_finite _

scoped instance instModuleFreeES (h : IPtHyp S) : Module.Free O ↥(ES h) := flatClosure_free _

scoped instance instModuleFlatES (h : IPtHyp S) : Module.Flat O ↥(ES h) := flatClosure_flat _

theorem ES_mono {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : IPtHyp S) (h' : IPtHyp S')
    (hle : S ≤ S') : ES h ≤ ES h' :=
  HopfAlgebra.characterClosure_mono O F A L (HopfAlgebra.ptSet_mono hle)

theorem counit_ES' (h : IPtHyp S) (e : ↥(ES h)) :
    letI := hopfES h
    Coalgebra.counit (R := O) e = Coalgebra.counit (R := O) (e : CartierDual O A) := rfl

abbrev ptsE (h : IPtHyp S) : Type := WithConv (↥(ES h) →ₐ[O] L)

noncomputable def chi [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (HopfAlgebra.evalQuot S)) :
    ptsE h ≃ (↥S →* L) :=
  (HopfAlgebra.exists_characterClosure_points_equiv O F A L).choose S h.sep h.inv_mem hev

theorem chi_mul [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (HopfAlgebra.evalQuot S)) (ψ ψ' : ptsE h) :
    letI := hopfES h
    chi h hev (ψ * ψ') = chi h hev ψ * chi h hev ψ' :=
  (HopfAlgebra.exists_characterClosure_points_equiv O F A L).choose_spec.1 S h.sep h.inv_mem hev
    (T4facts h).2.1 (T4facts h).2.2 ψ ψ'

theorem chi_one [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (HopfAlgebra.evalQuot S)) :
    letI := hopfES h
    chi h hev 1 = 1 := by
  letI := hopfES h

  set ψ₀ := (chi h hev).symm 1 with hψ₀
  have h0 : chi h hev ψ₀ = 1 := (chi h hev).apply_symm_apply 1
  have h1 : chi h hev (ψ₀ * 1) = chi h hev 1 := by rw [chi_mul, h0]; erw [one_mul]
  have h2 : ψ₀ * 1 = 1 := (chi h hev).injective h1
  erw [mul_one] at h2
  rw [← h0, h2]

theorem chi_eq_one_iff [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (HopfAlgebra.evalQuot S)) (ψ : ptsE h) :
    letI := hopfES h
    chi h hev ψ = 1 ↔ ψ = 1 := by
  letI := hopfES h
  rw [← chi_one h hev]
  exact (chi h hev).apply_eq_iff_eq

theorem chi_pow [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (HopfAlgebra.evalQuot S)) (ψ : ptsE h) (n : ℕ) :
    letI := hopfES h
    chi h hev (ψ ^ n) = chi h hev ψ ^ n := by
  letI := hopfES h
  induction n with
  | zero => erw [pow_zero, pow_zero]; exact chi_one h hev
  | succ n ih => erw [pow_succ, pow_succ, chi_mul, ih]

theorem chi_apply_pow_eq_one [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (HopfAlgebra.evalQuot S))
    (ψ : ptsE h) (ν : ↥S) (N : ℕ) (hν : ν ^ N = 1) :
    chi h hev ψ ν ^ N = 1 := by
  rw [← map_pow, hν, map_one]

theorem pts_pow_eq_one [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (HopfAlgebra.evalQuot S)) (n : ℕ)
    (hS : ∀ ν : ↥S, ν ^ n = 1) (ψ : ptsE h) :
    letI := hopfES h
    ψ ^ n = 1 := by
  letI := hopfES h
  rw [← chi_eq_one_iff h hev, chi_pow]
  ext ν
  rw [MonoidHom.pow_apply, ← map_pow, hS ν, map_one, MonoidHom.one_apply]

noncomputable def inclES {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : IPtHyp S) (h' : IPtHyp S')
    (hle : S ≤ S') : ↥(ES h) →ₐ[O] ↥(ES h') :=
  Subalgebra.inclusion (ES_mono h h' hle)

noncomputable def resE {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : IPtHyp S) (h' : IPtHyp S')
    (hle : S ≤ S') (ψ : ptsE h') : ptsE h :=
  WithConv.toConv (ψ.ofConv.comp (inclES h h' hle))

theorem resE_apply {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} (h : IPtHyp S) (h' : IPtHyp S')
    (hle : S ≤ S') (ψ : ptsE h') (e : ↥(ES h)) :
    (resE h h' hle ψ).ofConv e = ψ.ofConv (inclES h h' hle e) := rfl

theorem chi_resE {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} [Finite ↥S] [Finite ↥S']
    (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S')
    (hev : Function.Bijective (HopfAlgebra.evalQuot S)) (hev' : Function.Bijective (HopfAlgebra.evalQuot S'))
    (ψ : ptsE h') (ν : ↥S) :
    chi h hev (resE h h' hle ψ) ν = chi h' hev' ψ ⟨ν.1, hle ν.2⟩ :=
  (HopfAlgebra.exists_characterClosure_points_equiv O F A L).choose_spec.2.2 S S' h.sep h.inv_mem hev
    h'.sep h'.inv_mem hev' hle ψ ν

theorem resE_red {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} {Γ₀ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation L Γ₀)
    (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h')
    (hψ : letI := hopfES h'; ∀ e' : ↥(ES h'), v (ψ.ofConv e' - algebraMap O L (Coalgebra.counit (R := O) e')) < 1)
    (e : ↥(ES h)) :
    letI := hopfES h
    v ((resE h h' hle ψ).ofConv e - algebraMap O L (Coalgebra.counit (R := O) e)) < 1 :=
  hψ (inclES h h' hle e)

theorem resE_congr {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))} {Γ₀ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation L Γ₀)
    (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ ψ' : ptsE h')
    (hψ : ∀ e' : ↥(ES h'), v (ψ.ofConv e' - ψ'.ofConv e') < 1) (e : ↥(ES h)) :
    v ((resE h h' hle ψ).ofConv e - (resE h h' hle ψ').ofConv e) < 1 :=
  hψ (inclES h h' hle e)

private noncomputable abbrev _root_.P2MMultE.galO (σ : L ≃ₐ[F] L) : L →ₐ[O] L := (σ : L →ₐ[F] L).restrictScalars O

p2m_export "P2MMultE" "galO"
omit [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O] [IsFractionRing O F] in
private theorem _root_.P2MMultE.gal_algebraMap (σ : L ≃ₐ[F] L) (r : O) : σ (algebraMap O L r) = algebraMap O L r := by
  rw [IsScalarTower.algebraMap_apply O F L, AlgEquiv.commutes]

p2m_export "P2MMultE" "gal_algebraMap"

noncomputable def galE (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) : ptsE h :=
  WithConv.toConv ((galO σ).comp ψ.ofConv)

theorem galE_apply (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) (e : ↥(ES h)) :
    (galE h σ ψ).ofConv e = σ (ψ.ofConv e) := rfl

theorem galE_eq_self_iff (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ : ptsE h) :
    galE h σ ψ = ψ ↔ ∀ e, σ (ψ.ofConv e) = ψ.ofConv e := by
  constructor
  · intro hfix e
    rw [← galE_apply h σ ψ e, hfix]
  · intro hfix
    rw [← toConv_ofConv (galE h σ ψ), ← toConv_ofConv ψ]
    congr 1
    exact AlgHom.ext hfix

theorem chi_galE [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (HopfAlgebra.evalQuot S)) (σ : L ≃ₐ[F] L)
    (ψ : ptsE h) (ν ν' : ↥S) (hσ : ∀ x, (WithConv.ofConv ν'.1) x = σ ((WithConv.ofConv ν.1) x)) :
    chi h hev (galE h σ ψ) ν' = σ (chi h hev ψ ν) :=
  (HopfAlgebra.exists_characterClosure_points_equiv O F A L).choose_spec.2.1 S h.sep h.inv_mem hev σ ψ ν ν' hσ

theorem galE_mul (h : IPtHyp S) (σ : L ≃ₐ[F] L) (ψ ψ' : ptsE h) :
    letI := hopfES h
    galE h σ (ψ * ψ') = galE h σ ψ * galE h σ ψ' := by
  letI := hopfES h
  rw [← toConv_ofConv (galE h σ (ψ * ψ')), ← toConv_ofConv (galE h σ ψ * galE h σ ψ')]
  congr 1
  apply AlgHom.ext
  intro e
  rw [galE_apply, brConv_mul_apply, brConv_mul_apply]
  induction (Coalgebra.comul (R := O) e) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e₁ e₂ =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, galE_apply, galE_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galE_one (h : IPtHyp S) (σ : L ≃ₐ[F] L) :
    letI := hopfES h
    galE h σ 1 = 1 := by
  letI := hopfES h
  rw [← toConv_ofConv (galE h σ 1), ← toConv_ofConv (1 : ptsE h)]
  congr 1
  apply AlgHom.ext
  intro e
  rw [galE_apply, brConv_one_apply, gal_algebraMap]

theorem ptsE_mul_comm (h : IPtHyp S) (ψ ψ' : ptsE h) :
    letI := hopfES h
    ψ * ψ' = ψ' * ψ := by
  letI := hopfES h
  haveI := isCocommES h
  exact conv_mul_comm_of_isCocomm ψ ψ'

theorem char_gal_of_fixed [Finite ↥S] (h : IPtHyp S) (hev : Function.Bijective (HopfAlgebra.evalQuot S))
    (σ : L ≃ₐ[F] L) (hfix : ∀ ψ : ptsE h, galE h σ ψ = ψ)
    (f : ↥S →* L) (ν ν' : ↥S) (hσ : ∀ x, (WithConv.ofConv ν'.1) x = σ ((WithConv.ofConv ν.1) x)) :
    f ν' = σ (f ν) := by
  obtain ⟨ψ, rfl⟩ := (chi h hev).surjective f
  rw [← chi_galE h hev σ ψ ν ν' hσ, hfix]

theorem pow_of_galE_fixed [Finite ↥S] [IsAlgClosed L] [CharZero L] (h : IPtHyp S)
    (hev : Function.Bijective (HopfAlgebra.evalQuot S))
    (hcomm : ∀ μ μ' : ↥S, μ * μ' = μ' * μ)
    (N : ℕ) (hN : 0 < N) (htors : ∀ μ : ↥S, μ ^ N = 1)
    (σ : L ≃ₐ[F] L) (n : ℕ) (hn : ∀ ζ : L, ζ ^ N = 1 → σ ζ = ζ ^ n)
    (hfix : ∀ ψ : ptsE h, galE h σ ψ = ψ)
    (ν ν' : ↥S) (hσ : ∀ x, (WithConv.ofConv ν'.1) x = σ ((WithConv.ofConv ν.1) x)) :
    ν' = ν ^ n := by
  have hchar : ∀ f : ↥S →* L, f ν' = f (ν ^ n) := by
    intro f
    rw [char_gal_of_fixed h hev σ hfix f ν ν' hσ, map_pow]
    apply hn
    rw [← map_pow, htors, map_one]
  letI : CommGroup ↥S :=
    { (inferInstance : Monoid ↥S) with
      mul_comm := hcomm
      inv := fun μ => μ ^ (N - 1)
      inv_mul_cancel := fun μ => by
        show μ ^ (N - 1) * μ = 1
        rw [← pow_succ, Nat.sub_add_cancel hN, htors] }
  by_contra hne
  have hne1 : ν' * (ν ^ n)⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.mp h1)
  haveI : NeZero (Monoid.exponent ↥S) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ↥S L hne1
  apply hφ
  have key := hchar ((Units.coeHom L).comp φ)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Units.coeHom_apply, Units.coeHom_apply] at key
  rw [map_mul, map_inv, Units.ext key, mul_inv_cancel]

end Facade
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade"

end P2MMultE
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE"

namespace P2MMultE

theorem multiplicativeTypeNat_of_forall_twist_eq_pow
    {R : Type*} [CommSemiring R] {H : Type*} [Semiring H] [Algebra R H]
    {L : Type*} [Semiring L] [Algebra R L]
    [Monoid (WithConv (H →ₐ[R] L))]
    {G : Type*} [Group G] {J : Type*} [AddCommGroup J] [DistribMulAction G J]
    (ρ : G → L → L)
    (M : AddSubgroup J) (e : WithConv (H →ₐ[R] L) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : G) (f g : WithConv (H →ₐ[R] L)),
      (∀ x : H, g.ofConv x = ρ σ (f.ofConv x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (hex : ∀ (σ : G) (f : WithConv (H →ₐ[R] L)),
      ∃ g : WithConv (H →ₐ[R] L), ∀ x : H, g.ofConv x = ρ σ (f.ofConv x))
    (I : Subgroup G) (n : G → ℕ) (W : AddSubgroup J) (hW : W ≤ M)
    (hdual : ∀ τ ∈ I, ∀ f g : WithConv (H →ₐ[R] L),
      (∀ x : H, g.ofConv x = ρ τ (f.ofConv x)) → ((e f : ↥M) : J) ∈ W → g = f ^ n τ) :
    ModularCurve.MultiplicativeTypeNat I n W := by
  intro τ hτ x hx
  set f : WithConv (H →ₐ[R] L) := e.symm ⟨x, hW hx⟩ with hf
  have hef : ((e f : ↥M) : J) = x := by rw [hf, Equiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := hex τ f
  have h1 : ((e g : ↥M) : J) = τ • x := by rw [he_act τ f g hg, hef]
  have h2 : g = f ^ n τ := hdual τ hτ f g hg (hef ▸ hx)
  have he_one : (e 1 : ↥M) = 0 := by
    have h11 := he_add 1 1
    rw [one_mul] at h11
    exact left_eq_add.mp h11
  have he_pow : ∀ k : ℕ, ((e (f ^ k) : ↥M) : J) = k • x := by
    intro k
    induction k with
    | zero => rw [pow_zero, he_one, zero_smul]; rfl
    | succ k ih => rw [pow_succ, he_add, AddSubgroup.coe_add, ih, hef, succ_nsmul]
  rw [← h1, h2, he_pow]

theorem multiplicativeTypeNat_of_forall_twist_eq_pow'
    {R : Type*} [CommSemiring R] {H : Type*} [Semiring H] [Algebra R H]
    {K : Type*} [CommSemiring K] [Algebra R K]
    {L : Type*} [Semiring L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [Monoid (WithConv (H →ₐ[R] L))]
    {J : Type*} [AddCommGroup J] [DistribMulAction (L ≃ₐ[K] L) J]
    (M : AddSubgroup J) (e : WithConv (H →ₐ[R] L) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (H →ₐ[R] L)),
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (I : Subgroup (L ≃ₐ[K] L)) (n : (L ≃ₐ[K] L) → ℕ) (W : AddSubgroup J) (hW : W ≤ M)
    (hdual : ∀ τ ∈ I, ∀ f g : WithConv (H →ₐ[R] L),
      (∀ x : H, g x = τ (f x)) → ((e f : ↥M) : J) ∈ W → g = f ^ n τ) :
    ModularCurve.MultiplicativeTypeNat I n W :=
  multiplicativeTypeNat_of_forall_twist_eq_pow (fun σ : L ≃ₐ[K] L => (σ : L → L)) M e he_add he_act
    (fun σ f => ⟨WithConv.toConv (((σ : L →ₐ[K] L).restrictScalars R).comp f.ofConv), fun _ => rfl⟩)
    I n W hW hdual

end P2MMultE
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE"

section P9_EVLITE
set_option autoImplicit false

noncomputable section
open scoped TensorProduct Pointwise

namespace P2MMultEv

variable (q : ℕ) [Fact q.Prime]
variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
  [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
  [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]

local notation "ℚ̄" => AlgebraicClosure ℚ

abbrev Pts : Type := WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)

scoped instance : IsDiscreteValuationRing (GaloisRep.ratLocalizedAt q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out

scoped instance instFreeH : Module.Free (GaloisRep.ratLocalizedAt q) H := Module.free_of_flat_of_isLocalRing

theorem finite_pts : Finite (Pts q H) := by
  apply Nat.finite_of_card_ne_zero
  rw [GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf q H]
  haveI : Nontrivial H := by
    have h := Bialgebra.counit_one (R := GaloisRep.ratLocalizedAt q) (A := H)
    refine ⟨⟨1, 0, fun h10 => ?_⟩⟩
    have : (Coalgebra.counit (R := GaloisRep.ratLocalizedAt q) (A := H)) 1 = (Coalgebra.counit (R := GaloisRep.ratLocalizedAt q) (A := H)) 0 := by rw [h10]
    rw [h, map_zero] at this
    exact one_ne_zero this
  exact Module.finrank_pos.ne'

theorem gal_algebraMap (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (r : GaloisRep.ratLocalizedAt q) :
    σ (algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ r) = algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ r := by
  rw [IsScalarTower.algebraMap_apply (GaloisRep.ratLocalizedAt q) ℚ ℚ̄ r]
  exact σ.commutes _

theorem evGen_bijective :
    Function.Bijective (P2MMultSAdapt.evGen (GaloisRep.ratLocalizedAt q) ℚ̄ H) :=
  GaloisRep.bijective_lift_pi_algHom_of_finiteFlatHopf q H

section Bytes

variable {J : Type} [AddCommGroup J] [DistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) J]
variable (M : AddSubgroup J) (e : Pts q H ≃ ↥M) (he_add : ∀ f g, e (f * g) = e f + e g)
include he_add

theorem e_one : e 1 = 0 := by
  have h := he_add 1 1
  erw [one_mul] at h
  exact left_eq_add.mp h

theorem e_pow (f : Pts q H) (n : ℕ) : e (f ^ n) = n • e f := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact e_one q H M e he_add
  | succ n ih => rw [pow_succ, he_add, ih, succ_nsmul]

theorem pow_eq_one_of_torsion (m : ℕ) (htors : ∀ x : ↥M, q ^ m • x = 0) (f : Pts q H) : f ^ (q ^ m) = 1 := by
  apply e.injective
  rw [e_pow q H M e he_add, e_one q H M e he_add]
  exact htors (e f)

end Bytes
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE"

section Decomposition

variable (A : ValuationSubring ℚ̄) {σ : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hσ : σ ∈ A.decompositionSubgroup ℚ)
include hσ

omit [Fact q.Prime] in
theorem mem_iff_of_mem_decomposition (z : ℚ̄) : σ z ∈ A ↔ z ∈ A := by
  have h1 : σ • (A : ValuationSubring ℚ̄) = A := hσ
  constructor
  · intro hz
    have : σ z ∈ σ • A := by rw [h1]; exact hz
    obtain ⟨w, hw, hwz⟩ := this
    have : w = z := σ.injective hwz
    rw [← this]; exact hw
  · intro hz
    rw [← h1]
    exact ⟨z, hz, rfl⟩

def resA : ↥A →+* ↥A where
  toFun a := ⟨σ (a : ℚ̄), (mem_iff_of_mem_decomposition A hσ _).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

def resAinv : ↥A →+* ↥A where
  toFun a := ⟨σ.symm (a : ℚ̄), by
    rw [← mem_iff_of_mem_decomposition A hσ, AlgEquiv.apply_symm_apply]; exact a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

omit [Fact q.Prime] in
theorem resAinv_resA (a : ↥A) : resAinv A hσ (resA A hσ a) = a :=
  Subtype.ext (σ.symm_apply_apply (a : ℚ̄))

omit [Fact q.Prime] in

theorem valuation_lt_one_of_mem_decomposition {y : ℚ̄} (hy : A.valuation y < 1) : A.valuation (σ y) < 1 := by
  have hyA : y ∈ A := (A.valuation_le_one_iff y).mp hy.le
  have hσyA : σ y ∈ A := (mem_iff_of_mem_decomposition A hσ y).mpr hyA
  have h1 : (⟨y, hyA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (A.valuation_lt_one_iff _).mpr hy
  suffices h2 : (⟨σ y, hσyA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A from (A.valuation_lt_one_iff _).mp h2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
  intro hu
  apply h1
  have : (⟨σ y, hσyA⟩ : ↥A) = resA A hσ ⟨y, hyA⟩ := rfl
  rw [this] at hu
  have := hu.map (resAinv A hσ)
  rwa [resAinv_resA] at this

end Decomposition
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE"

end P2MMultEv
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"
end
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

end P9_EVLITE
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

section P9_INJ

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace P2MMultFinal

open WithConv
open scoped TensorProduct

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section RedMul

variable {O : Type*} [CommRing O] [Algebra O ℚ̄] {C : Type*} [CommRing C] [Bialgebra O C]

theorem conv_one_apply (c : C) : (1 : WithConv (C →ₐ[O] ℚ̄)) c = algebraMap O ℚ̄ (Coalgebra.counit c) :=
  AlgHom.convOne_apply c

theorem conv_mul_apply_repr (f g : WithConv (C →ₐ[O] ℚ̄)) {c : C} {ι : Type*} (𝓡 : Coalgebra.Repr O c ι) :
    (f * g) c = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  change (Algebra.TensorProduct.lmul' O (S := ℚ̄)) (Algebra.TensorProduct.map f.ofConv g.ofConv (Coalgebra.comul c)) = _
  rw [← 𝓡.eq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]

variable (A : ValuationSubring ℚ̄)

theorem red_of_congr_of_mul_eq_one (hint : ∀ (φ : C →ₐ[O] ℚ̄) (c : C), A.valuation (φ c) ≤ 1)
    (f g g' : WithConv (C →ₐ[O] ℚ̄)) (hgg' : g * g' = 1)
    (hfg : ∀ c : C, A.valuation (f c - g c) < 1) (c : C) :
    A.valuation ((f * g') c - algebraMap O ℚ̄ (Coalgebra.counit c)) < 1 := by
  classical
  have e1 : algebraMap O ℚ̄ (Coalgebra.counit c) = (g * g') c := by rw [hgg', conv_one_apply]
  rw [e1, conv_mul_apply_repr f g' (Coalgebra.Repr.arbitrary O c), conv_mul_apply_repr g g' (Coalgebra.Repr.arbitrary O c),
    ← Finset.sum_sub_distrib]
  refine A.valuation.map_sum_lt one_ne_zero fun i _ => ?_
  rw [← sub_mul, map_mul]
  calc A.valuation (f _ - g _) * A.valuation (g' _)
      ≤ A.valuation (f _ - g _) * 1 := mul_le_mul' le_rfl (hint g'.ofConv _)
    _ < 1 := by rw [mul_one]; exact hfg _

end RedMul
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

section IRes

variable (A : ValuationSubring ℚ̄)

theorem valuation_sub_lt_one_of_mem_inertia {τ : Gal} (hτ : τ ∈ A.inertiaSubgroupIn ℚ) {y : ℚ̄} (hy : y ∈ A) :
    A.valuation (τ y - y) < 1 := by
  obtain ⟨τ', hτ', rfl⟩ := Subgroup.mem_map.mp hτ

  have hker : MulSemiringAction.toRingAut (↥(A.decompositionSubgroup ℚ)) (IsLocalRing.ResidueField ↥A) τ' = 1 :=
    (MonoidHom.mem_ker).mp hτ'
  have hres : IsLocalRing.residue ↥A (τ' • (⟨y, hy⟩ : ↥A)) = IsLocalRing.residue ↥A ⟨y, hy⟩ := by
    have := RingEquiv.congr_fun (congrArg (fun f : RingAut _ => (f : _ ≃+* _)) hker) (IsLocalRing.residue ↥A ⟨y, hy⟩)
    simpa using this
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at hres
  have := (A.valuation_lt_one_iff _).mp hres
  first | (simpa using this) | exact this | (refine lt_of_eq_of_lt ?_ this; rfl)

end IRes
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

end P2MMultFinal
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"
end P9_INJ
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

section P9_INJ2

set_option autoImplicit false
set_option maxHeartbeats 51200000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

namespace P2MMultFinal

open WithConv
open scoped TensorProduct

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (q : ℕ) [Fact q.Prime]
variable (Aval : ValuationSubring ℚ̄) [Fact (((q : ℕ) : ℚ̄) ∈ Aval.nonunits)]
  [Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aval.nonunits)]
variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
  [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
  [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
  [Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄))]
variable {J : Type} [AddCommGroup J] [DistribMulAction Gal J]
variable (M : AddSubgroup J) (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) ≃ ↥M)
  (he_add : ∀ f g, e (f * g) = e f + e g)

theorem ptsF_pow_eq_one (n : ℕ) (htorsH : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄), f ^ n = 1)
    (ν : P2MMultSFacade.PtsF q Aval H) : ν ^ n = 1 := by
  obtain ⟨κ, rfl⟩ := P2MMultSAdapt.liftPt_surjective (K := P2MMultOR.decRing Aval) (S := P2MMultO.decField Aval) ν
  obtain ⟨φ, rfl⟩ := P2MMultSAdapt.liftPt_surjective (K := GaloisRep.ratLocalizedAt q) (S := P2MMultOR.decRing Aval) κ
  rw [← P2MMultSAdapt.liftPt_pow, ← P2MMultSAdapt.liftPt_pow, htorsH, P2MMultSAdapt.liftPt_one,
    P2MMultSAdapt.liftPt_one]

theorem submonoid_pow_eq_one (n : ℕ) (htorsH : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄), f ^ n = 1)
    (S : Submonoid (P2MMultSFacade.PtsF q Aval H)) (ν : ↥S) : ν ^ n = 1 :=
  Subtype.ext (by
    rw [show ((ν ^ n : ↥S) : P2MMultSFacade.PtsF q Aval H) = (ν : P2MMultSFacade.PtsF q Aval H) ^ n from
        SubmonoidClass.coe_pow ν n,
      show ((1 : ↥S) : P2MMultSFacade.PtsF q Aval H) = 1 from OneMemClass.coe_one S]
    exact ptsF_pow_eq_one q Aval H n htorsH ν.1)

theorem KNF_mono {N N' : AddSubgroup J} (hNN' : N ≤ N') :
    P2MMultSFacade.KNF q Aval H M e he_add N ≤ P2MMultSFacade.KNF q Aval H M e he_add N' := by
  intro ν hν
  rw [P2MMultSFacade.mem_KNF_iff_lab] at hν ⊢
  exact hNN' hν

def RedInj {S : Submonoid (P2MMultSFacade.PtsF q Aval H)} (h : P2MMultE.IPtHyp S) : Prop :=
  ∀ ψ ψ' : P2MMultE.ptsE h, (∀ s, Aval.valuation ((ofConv ψ) s - (ofConv ψ') s) < 1) → ψ = ψ'

theorem galE_eq_of_chi_trivial
    (m : ℕ) (htorsH : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄), f ^ (q ^ m) = 1)
    (n : Gal → ℕ) (hn : ∀ (σ : Gal) (ζ : ℚ̄), ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ)
    (N N' : AddSubgroup J)
    (h' : P2MMultE.IPtHyp (P2MMultSFacade.KNF q Aval H M e he_add N'))
    (hev' : Function.Bijective (P2MMultE.evQ (P2MMultSFacade.KNF q Aval H M e he_add N')))
    (hχS : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ →
      ∀ ν μ : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'),
        (∀ x, (ofConv μ.1) x = σ ((ofConv ν.1) x)) →
        ∃ t : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'),
          t.1 ∈ P2MMultSFacade.KNF q Aval H M e he_add N ∧ μ = ν ^ n σ * t)
    (hstab' : ∀ (σ : Gal) (hσ : σ ∈ Aval.decompositionSubgroup ℚ),
      ∀ ν ∈ P2MMultSFacade.KNF q Aval H M e he_add N',
        toConv (((P2MMultSAdapt.galF Aval hσ) : ℚ̄ →ₐ[P2MMultO.decField Aval] ℚ̄).comp (ofConv ν))
          ∈ P2MMultSFacade.KNF q Aval H M e he_add N')
    (ρ : P2MMultE.ptsE h')
    (hχ1 : ∀ t : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'),
      t.1 ∈ P2MMultSFacade.KNF q Aval H M e he_add N → P2MMultE.chi h' hev' ρ t = 1)
    (σ : Gal) (hσ : σ ∈ Aval.decompositionSubgroup ℚ) :
    P2MMultE.galE h' (P2MMultSAdapt.galF Aval hσ) ρ = ρ := by
  haveI : Finite ↥(P2MMultSFacade.KNF q Aval H M e he_add N') := inferInstance
  have htorsS' : ∀ ν : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'), ν ^ (q ^ m) = 1 :=
    submonoid_pow_eq_one q Aval H (q ^ m) htorsH _
  apply (P2MMultE.chi h' hev').injective
  ext μ
  have hσi : σ⁻¹ ∈ Aval.decompositionSubgroup ℚ := Subgroup.inv_mem _ hσ
  let ν : ↥(P2MMultSFacade.KNF q Aval H M e he_add N') :=
    ⟨toConv (((P2MMultSAdapt.galF Aval hσi) : ℚ̄ →ₐ[P2MMultO.decField Aval] ℚ̄).comp (ofConv μ.1)),
      hstab' σ⁻¹ hσi μ.1 μ.2⟩
  have hσν : ∀ x, (ofConv μ.1) x = (P2MMultSAdapt.galF Aval hσ) ((ofConv ν.1) x) := by
    intro x
    show (ofConv μ.1) x = σ (σ⁻¹ ((ofConv μ.1) x))
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rw [P2MMultE.chi_galE h' hev' (P2MMultSAdapt.galF Aval hσ) ρ ν μ hσν]
  have hval : (P2MMultE.chi h' hev' ρ ν) ^ (q ^ m) = 1 :=
    P2MMultE.chi_apply_pow_eq_one h' hev' ρ ν _ (htorsS' ν)
  rw [P2MMultSAdapt.galF_apply, hn σ _ hval, ← map_pow]
  obtain ⟨t, htN, hμ⟩ := hχS σ hσ ν μ (fun x => hσν x)
  rw [hμ, map_mul, hχ1 t htN, mul_one]

theorem inj_step (hq2 : q ≠ 2)
    (m : ℕ) (htorsH : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄), f ^ (q ^ m) = 1)
    (n : Gal → ℕ) (hn : ∀ (σ : Gal) (ζ : ℚ̄), ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ)
    (N N' : AddSubgroup J) (hNN' : N ≤ N')
    (h : P2MMultE.IPtHyp (P2MMultSFacade.KNF q Aval H M e he_add N))
    (h' : P2MMultE.IPtHyp (P2MMultSFacade.KNF q Aval H M e he_add N'))
    (hev : Function.Bijective (P2MMultE.evQ (P2MMultSFacade.KNF q Aval H M e he_add N)))
    (hev' : Function.Bijective (P2MMultE.evQ (P2MMultSFacade.KNF q Aval H M e he_add N')))
    (hχS : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ →
      ∀ ν μ : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'),
        (∀ x, (ofConv μ.1) x = σ ((ofConv ν.1) x)) →
        ∃ t : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'),
          t.1 ∈ P2MMultSFacade.KNF q Aval H M e he_add N ∧ μ = ν ^ n σ * t)
    (hstab' : ∀ (σ : Gal) (hσ : σ ∈ Aval.decompositionSubgroup ℚ),
      ∀ ν ∈ P2MMultSFacade.KNF q Aval H M e he_add N',
        toConv (((P2MMultSAdapt.galF Aval hσ) : ℚ̄ →ₐ[P2MMultO.decField Aval] ℚ̄).comp (ofConv ν))
          ∈ P2MMultSFacade.KNF q Aval H M e he_add N')
    (IH : RedInj q Aval H h) : RedInj q Aval H h' := by
  classical
  letI hE' := P2MMultE.hopfES h'
  letI hE := P2MMultE.hopfES h
  haveI := P2MMultE.isCocommES h'
  have hA : ((q : ℕ) : ℚ̄) ∈ Aval.nonunits := Fact.out
  have hle : P2MMultSFacade.KNF q Aval H M e he_add N ≤ P2MMultSFacade.KNF q Aval H M e he_add N' :=
    KNF_mono q Aval H M e he_add hNN'
  haveI : Finite ↥(P2MMultSFacade.KNF q Aval H M e he_add N) := inferInstance
  haveI : Finite ↥(P2MMultSFacade.KNF q Aval H M e he_add N') := inferInstance
  intro ψ ψ' hcong
  have htorsS' : ∀ ν : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'), ν ^ (q ^ m) = 1 :=
    submonoid_pow_eq_one q Aval H (q ^ m) htorsH _
  have hqm : 1 ≤ q ^ m := Nat.one_le_pow _ _ (Fact.out : q.Prime).pos
  have hψ'pow : ψ' ^ (q ^ m) = 1 := P2MMultE.pts_pow_eq_one h' hev' _ htorsS' ψ'
  have hgg' : ψ' * ψ' ^ (q ^ m - 1) = 1 := by
    have hp : ψ' ^ (q ^ m - 1 + 1) = ψ' * ψ' ^ (q ^ m - 1) := pow_succ' _ _
    rw [← hp, Nat.sub_add_cancel hqm, hψ'pow]

  have hint : ∀ (φ : ↥(P2MMultE.ES h') →ₐ[P2MMultOR.decRing Aval] ℚ̄) (s : ↥(P2MMultE.ES h')), Aval.valuation (φ s) ≤ 1 :=
    fun φ s => (Aval.valuation_le_one_iff _).mpr (P2MMultSAdapt.apply_mem_A Aval φ s)
  have hρred : ∀ s, Aval.valuation ((ψ * ψ' ^ (q ^ m - 1)) s
      - algebraMap (P2MMultOR.decRing Aval) ℚ̄ (Coalgebra.counit s)) < 1 :=
    red_of_congr_of_mul_eq_one Aval hint ψ ψ' (ψ' ^ (q ^ m - 1)) hgg' hcong

  have hρN : P2MMultE.resE h h' hle (ψ * ψ' ^ (q ^ m - 1)) = 1 := by
    apply IH
    intro s
    rw [conv_one_apply]
    exact P2MMultE.resE_red Aval.valuation h h' hle _ hρred s

  have hχ1 : ∀ t : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'),
      t.1 ∈ P2MMultSFacade.KNF q Aval H M e he_add N → P2MMultE.chi h' hev' (ψ * ψ' ^ (q ^ m - 1)) t = 1 := by
    intro t ht
    have h1 := P2MMultE.chi_resE h h' hle hev hev' (ψ * ψ' ^ (q ^ m - 1)) ⟨t.1, ht⟩
    rw [hρN, P2MMultE.chi_one] at h1
    exact h1.symm

  have hρfix : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ → ∀ s, σ ((ψ * ψ' ^ (q ^ m - 1)) s) = (ψ * ψ' ^ (q ^ m - 1)) s :=
    fun σ hσ => (P2MMultE.galE_eq_self_iff h' (P2MMultSAdapt.galF Aval hσ) _).mp
      (galE_eq_of_chi_trivial q Aval H M e he_add m htorsH n hn N N' h' hev' hχS hstab' _ hχ1 σ hσ)

  obtain ⟨x₀, hx₀ρ, -, hx₀pow, hx₀red⟩ := P2MMultSAdapt.exists_OPt_of_fixed Aval (ψ * ψ' ^ (q ^ m - 1)) hρfix
  have hρpow : (ψ * ψ' ^ (q ^ m - 1)) ^ (q ^ m) = 1 := P2MMultE.pts_pow_eq_one h' hev' _ htorsS' _
  have hx₀1 : x₀ = 1 :=
    HopfAlgebra.point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal
      (P2MMultOR.decRing Aval) q hq2 (P2MMultOR.irreducible_ell Aval q hA)
      ↥(P2MMultE.ES h') x₀ (hx₀red hρred) m ((hx₀pow _).mp hρpow)
  have hρ1 : ψ * ψ' ^ (q ^ m - 1) = 1 := by rw [← hx₀ρ, hx₀1, P2MMultSAdapt.toQbarPt_one]

  have e2 : ψ * 1 = ψ := mul_one _
  have e3 : ψ * (ψ' * ψ' ^ (q ^ m - 1)) = (ψ * ψ') * ψ' ^ (q ^ m - 1) := (mul_assoc _ _ _).symm
  have e4 : ψ * ψ' = ψ' * ψ := P2MMultE.conv_mul_comm_of_isCocomm ψ ψ'
  have e5 : (ψ' * ψ) * ψ' ^ (q ^ m - 1) = ψ' * (ψ * ψ' ^ (q ^ m - 1)) := mul_assoc _ _ _
  have e6 : ψ' * 1 = ψ' := mul_one _
  calc ψ = ψ * 1 := e2.symm
    _ = ψ * (ψ' * ψ' ^ (q ^ m - 1)) := by rw [hgg']
    _ = (ψ * ψ') * ψ' ^ (q ^ m - 1) := e3
    _ = (ψ' * ψ) * ψ' ^ (q ^ m - 1) := by rw [e4]
    _ = ψ' * (ψ * ψ' ^ (q ^ m - 1)) := e5
    _ = ψ' * 1 := by rw [hρ1]
    _ = ψ' := e6

end P2MMultFinal
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"
end P9_INJ2
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

section P9_INJ3

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

namespace P2MMultFinal

open WithConv
open scoped TensorProduct

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (q : ℕ) [Fact q.Prime]
variable (Aval : ValuationSubring ℚ̄) [Fact (((q : ℕ) : ℚ̄) ∈ Aval.nonunits)]
  [Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aval.nonunits)]
variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
  [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
  [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
  [Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄))]
variable {J : Type} [AddCommGroup J] [DistribMulAction Gal J]
variable (M : AddSubgroup J) (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) ≃ ↥M)
  (he_add : ∀ f g, e (f * g) = e f + e g)
  (he_act : ∀ (σ : Gal) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)),
    (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))

noncomputable abbrev LL (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) : P2MMultSFacade.PtsF q Aval H :=
  P2MMultSAdapt.liftPt (S := P2MMultO.decField Aval) (P2MMultSAdapt.liftPt (S := P2MMultOR.decRing Aval) φ)

omit [Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aval.nonunits)] [Module.Finite (GaloisRep.ratLocalizedAt q) H]
  [Module.Flat (GaloisRep.ratLocalizedAt q) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
  [Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄))] in
theorem LL_surjective : Function.Surjective (LL q Aval H) := by
  intro ν
  obtain ⟨κ, rfl⟩ := P2MMultSAdapt.liftPt_surjective (K := P2MMultOR.decRing Aval) (S := P2MMultO.decField Aval) ν
  obtain ⟨φ, rfl⟩ := P2MMultSAdapt.liftPt_surjective (K := GaloisRep.ratLocalizedAt q) (S := P2MMultOR.decRing Aval) κ
  exact ⟨φ, rfl⟩

theorem LL_mul (φ ψ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) : LL q Aval H (φ * ψ) = LL q Aval H φ * LL q Aval H ψ := by
  rw [LL, P2MMultSAdapt.liftPt_mul, P2MMultSAdapt.liftPt_mul]

theorem LL_pow (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) (k : ℕ) : LL q Aval H (φ ^ k) = LL q Aval H φ ^ k := by
  rw [LL, P2MMultSAdapt.liftPt_pow, P2MMultSAdapt.liftPt_pow]

theorem lab_LL (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    P2MMultSFacade.lab q Aval H M e ((P2MMultSAdapt.liftPtEquiv (S := P2MMultO.decField Aval)).symm (LL q Aval H φ))
      = ((e φ : ↥M) : J) := by
  rw [LL, ← P2MMultSAdapt.liftPtEquiv_apply, Equiv.symm_apply_apply, P2MMultSFacade.lab_liftPt]

theorem LL_mem_KNF_iff (N : AddSubgroup J) (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    LL q Aval H φ ∈ P2MMultSFacade.KNF q Aval H M e he_add N ↔ ((e φ : ↥M) : J) ∈ N := by
  rw [P2MMultSFacade.mem_KNF_iff_lab, lab_LL]

theorem LL_twist {σ : Gal} (hσ : σ ∈ Aval.decompositionSubgroup ℚ) (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) :
    LL q Aval H (toConv (((σ : ℚ̄ →ₐ[ℚ] ℚ̄).restrictScalars (GaloisRep.ratLocalizedAt q)).comp φ.ofConv))
      = toConv (((P2MMultSAdapt.galF Aval hσ) : ℚ̄ →ₐ[P2MMultO.decField Aval] ℚ̄).comp (LL q Aval H φ).ofConv) := by
  apply WithConv.ext
  rw [WithConv.ofConv_toConv, P2MMultSAdapt.comp_liftPt, P2MMultSAdapt.galF_restrictScalars]
  show _ = (P2MMultSAdapt.liftPt (S := P2MMultO.decField Aval)
    (toConv ((P2MMultSAdapt.galO Aval hσ).comp (P2MMultSAdapt.liftPt (S := P2MMultOR.decRing Aval) φ).ofConv))).ofConv
  rw [P2MMultSAdapt.comp_liftPt]
  rfl

include he_add he_act in

theorem chiS_of_chi (m : ℕ) (htorsH : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄), f ^ (q ^ m) = 1)
    (n : Gal → ℕ) (N N' : AddSubgroup J)
    (hχ : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ → ∀ x ∈ N', σ • x - n σ • x ∈ N)
    (σ : Gal) (hσ : σ ∈ Aval.decompositionSubgroup ℚ)
    (ν μ : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'))
    (hμ : ∀ x, (ofConv μ.1) x = σ ((ofConv ν.1) x)) :
    ∃ t : ↥(P2MMultSFacade.KNF q Aval H M e he_add N'),
      t.1 ∈ P2MMultSFacade.KNF q Aval H M e he_add N ∧ μ = ν ^ n σ * t := by
  have hqm : 1 ≤ q ^ m := Nat.one_le_pow _ _ (Fact.out : q.Prime).pos
  obtain ⟨φ, hφ⟩ := LL_surjective q Aval H ν.1

  set φσ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) :=
    toConv (((σ : ℚ̄ →ₐ[ℚ] ℚ̄).restrictScalars (GaloisRep.ratLocalizedAt q)).comp φ.ofConv) with hφσ
  have hμ' : μ.1 = LL q Aval H φσ := by
    rw [LL_twist q Aval H hσ φ, hφ]
    apply WithConv.ext; apply AlgHom.ext; intro x
    rw [WithConv.ofConv_toConv]
    exact hμ x
  have hφN' : ((e φ : ↥M) : J) ∈ N' := by rw [← LL_mem_KNF_iff q Aval H M e he_add N', hφ]; exact ν.2

  let k : ℕ := n σ * (q ^ m - 1)
  refine ⟨⟨μ.1 * ν.1 ^ k, mul_mem μ.2 (pow_mem ν.2 k)⟩, ?_, ?_⟩
  ·
    show μ.1 * ν.1 ^ k ∈ _
    rw [hμ', ← hφ, ← LL_pow, ← LL_mul, LL_mem_KNF_iff, he_add, AddSubgroup.coe_add, he_act σ φ φσ (fun _ => rfl),
      P2MMultEv.e_pow q H M e he_add, AddSubgroup.coe_nsmul]
    have htor : (q ^ m) • ((e φ : ↥M) : J) = 0 := by
      rw [← AddSubgroup.coe_nsmul, ← P2MMultEv.e_pow q H M e he_add, htorsH, P2MMultEv.e_one q H M e he_add]; rfl
    have key : σ • ((e φ : ↥M) : J) + k • ((e φ : ↥M) : J)
        = (σ • ((e φ : ↥M) : J) - n σ • ((e φ : ↥M) : J)) + n σ • ((q ^ m) • ((e φ : ↥M) : J)) := by
      rw [← mul_nsmul', show n σ * q ^ m = n σ + k from by
        simp only [k]; rw [Nat.mul_sub, mul_one, Nat.add_sub_cancel' (Nat.le_mul_of_pos_right _ (by omega))], add_nsmul]
      abel
    rw [key, htor, nsmul_zero, add_zero]
    exact hχ σ hσ _ hφN'
  · apply Subtype.ext
    show μ.1 = (ν ^ n σ).1 * (μ.1 * ν.1 ^ k)
    have harith : n σ + k = n σ * q ^ m := by
      simp only [k]; rw [Nat.mul_sub, mul_one, Nat.add_sub_cancel' (Nat.le_mul_of_pos_right _ (by omega))]
    have hcp : (ν ^ n σ).1 = ν.1 ^ n σ := SubmonoidClass.coe_pow _ _
    have hc : ν.1 ^ n σ * μ.1 = μ.1 * ν.1 ^ n σ := P2MMultE.conv_mul_comm_of_isCocomm _ _
    have ha1 : ν.1 ^ n σ * (μ.1 * ν.1 ^ k) = (ν.1 ^ n σ * μ.1) * ν.1 ^ k := (mul_assoc _ _ _).symm
    have ha2 : (μ.1 * ν.1 ^ n σ) * ν.1 ^ k = μ.1 * (ν.1 ^ n σ * ν.1 ^ k) := mul_assoc _ _ _
    have hpa : ν.1 ^ (n σ + k) = ν.1 ^ n σ * ν.1 ^ k := pow_add _ _ _
    have hpm : ν.1 ^ (n σ * q ^ m) = (ν.1 ^ (q ^ m)) ^ n σ := pow_mul' _ _ _
    have hone : ν.1 ^ (n σ * q ^ m) = 1 := by
      rw [hpm, ptsF_pow_eq_one q Aval H (q ^ m) htorsH]; exact one_pow _
    have hm1 : μ.1 * 1 = μ.1 := mul_one _
    symm
    calc (ν ^ n σ).1 * (μ.1 * ν.1 ^ k) = ν.1 ^ n σ * (μ.1 * ν.1 ^ k) := by rw [hcp]
      _ = (ν.1 ^ n σ * μ.1) * ν.1 ^ k := ha1
      _ = (μ.1 * ν.1 ^ n σ) * ν.1 ^ k := by rw [hc]
      _ = μ.1 * (ν.1 ^ n σ * ν.1 ^ k) := ha2
      _ = μ.1 * ν.1 ^ (n σ + k) := by rw [← hpa]
      _ = μ.1 * ν.1 ^ (n σ * q ^ m) := by rw [harith]
      _ = μ.1 * 1 := by rw [hone]
      _ = μ.1 := hm1

end P2MMultFinal
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"
end P9_INJ3
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

section P9_INJ4

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

namespace P2MMultFinal

open WithConv
open scoped TensorProduct

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (q : ℕ) [Fact q.Prime]
variable (Aval : ValuationSubring ℚ̄) [Fact (((q : ℕ) : ℚ̄) ∈ Aval.nonunits)]
  [Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aval.nonunits)]
variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
  [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
  [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
  [Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄))]
variable {J : Type} [AddCommGroup J] [DistribMulAction Gal J]
variable (M : AddSubgroup J) (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) ≃ ↥M)
  (he_add : ∀ f g, e (f * g) = e f + e g)

include he_add in

theorem inj_base (N : AddSubgroup J) (hNbot : ∀ x : J, x ∈ N → x = 0)
    (h : P2MMultE.IPtHyp (P2MMultSFacade.KNF q Aval H M e he_add N))
    (hev : Function.Bijective (P2MMultE.evQ (P2MMultSFacade.KNF q Aval H M e he_add N))) :
    RedInj q Aval H h := by
  haveI : Finite ↥(P2MMultSFacade.KNF q Aval H M e he_add N) := inferInstance
  intro ψ ψ' _
  apply (P2MMultE.chi h hev).injective
  ext ν
  have hν : ν = 1 := by
    apply Subtype.ext
    obtain ⟨φ, hφ⟩ := LL_surjective q Aval H ν.1
    have h2 : ((e φ : ↥M) : J) ∈ N := by rw [← LL_mem_KNF_iff q Aval H M e he_add N, hφ]; exact ν.2
    have h3 : φ = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [hNbot _ h2]
      exact (congrArg (fun x : ↥M => (x : J)) (P2MMultEv.e_one q H M e he_add)).symm
    rw [show ((1 : ↥(P2MMultSFacade.KNF q Aval H M e he_add N)) : P2MMultSFacade.PtsF q Aval H) = 1 from OneMemClass.coe_one _,
      ← hφ, h3, LL, P2MMultSAdapt.liftPt_one, P2MMultSAdapt.liftPt_one]
  rw [hν, map_one, map_one]

theorem end_of_redInj (W : AddSubgroup J)
    (h : P2MMultE.IPtHyp (P2MMultSFacade.KNF q Aval H M e he_add W))
    (hRI : RedInj q Aval H h) :
    ∀ τ : Gal, τ ∈ Aval.inertiaSubgroupIn ℚ → ∀ ψ : P2MMultE.ptsE h, ∀ s, τ ((ofConv ψ) s) = (ofConv ψ) s := by
  letI := P2MMultE.hopfES h
  intro τ hτ ψ
  have hτD : τ ∈ Aval.decompositionSubgroup ℚ := by
    obtain ⟨τ', _, rfl⟩ := Subgroup.mem_map.mp hτ
    exact τ'.2
  have key : P2MMultE.galE h (P2MMultSAdapt.galF Aval hτD) ψ = ψ := by
    apply hRI
    intro s
    show Aval.valuation (τ ((ofConv ψ) s) - (ofConv ψ) s) < 1
    exact valuation_sub_lt_one_of_mem_inertia Aval hτ (P2MMultSAdapt.apply_mem_A Aval (ofConv ψ) s)
  exact (P2MMultE.galE_eq_self_iff h (P2MMultSAdapt.galF Aval hτD) ψ).mp key

end P2MMultFinal
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"
end P9_INJ4
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

section P13_HDUAL

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

namespace P2MMultFinal

open WithConv P2MMultSAdapt

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem mem_decompositionSubgroup_of_mem_inertiaSubgroupIn (Aval : ValuationSubring ℚ̄) {τ : Gal}
    (hτ : τ ∈ Aval.inertiaSubgroupIn ℚ) : τ ∈ Aval.decompositionSubgroup ℚ := by
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hτ
  exact x.2

theorem hdual_of_END
    (q : ℕ) [Fact q.Prime]
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
    (W : AddSubgroup J) (hWst : ∀ σ : Gal, σ ∈ Aval.decompositionSubgroup ℚ → ∀ x ∈ W, σ • x ∈ W)
    (N : ℕ) (hN0 : 0 < N) (htors : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄), f ^ N = 1)
    (n : Gal → ℕ) (hn : ∀ σ : Gal, ∀ ζ : ℚ̄, ζ ^ N = 1 → σ ζ = ζ ^ n σ)
    (h : P2MMultE.IPtHyp (P2MMultSFacade.KNF q Aval H M e he_add W))
    (hev : Function.Bijective (P2MMultE.evQ (P2MMultSFacade.KNF q Aval H M e he_add W)))
    (hEND : ∀ τ : Gal, τ ∈ Aval.inertiaSubgroupIn ℚ → ∀ ψ : P2MMultE.ptsE h, ∀ s,
      τ ((WithConv.ofConv ψ) s) = (WithConv.ofConv ψ) s) :
    ∀ τ : Gal, τ ∈ Aval.inertiaSubgroupIn ℚ → ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄),
      (∀ x : H, g x = τ (f x)) → ((e f : ↥M) : J) ∈ W → g = f ^ n τ := by
  intro τ hτ f g hfg hfW
  have hτD : τ ∈ Aval.decompositionSubgroup ℚ := mem_decompositionSubgroup_of_mem_inertiaSubgroupIn Aval hτ

  have hνf : liftPt (S := P2MMultO.decField Aval) (liftPt (S := P2MMultOR.decRing Aval) f)
      ∈ P2MMultSFacade.KNF q Aval H M e he_add W := by
    rw [P2MMultSFacade.liftPt_mem_KNF_iff, P2MMultSFacade.mem_KN_iff, P2MMultSFacade.lab_liftPt]
    exact hfW
  have hνg : liftPt (S := P2MMultO.decField Aval) (liftPt (S := P2MMultOR.decRing Aval) g)
      ∈ P2MMultSFacade.KNF q Aval H M e he_add W := by
    rw [P2MMultSFacade.liftPt_mem_KNF_iff, P2MMultSFacade.mem_KN_iff, P2MMultSFacade.lab_liftPt,
      he_act τ f g hfg]
    exact hWst τ hτD _ hfW

  have h1 : toConv (((galO Aval hτD).restrictScalars (GaloisRep.ratLocalizedAt q)).comp f.ofConv) = g :=
    WithConv.ext (AlgHom.ext fun x => (hfg x).symm)
  have h2 : (galO Aval hτD).comp (liftPt (S := P2MMultOR.decRing Aval) f).ofConv
      = (liftPt (S := P2MMultOR.decRing Aval) g).ofConv := by
    rw [comp_liftPt, h1]
  have h3 : (galF Aval hτD : ℚ̄ →ₐ[P2MMultO.decField Aval] ℚ̄).comp
        (liftPt (S := P2MMultO.decField Aval) (liftPt (S := P2MMultOR.decRing Aval) f)).ofConv
      = (liftPt (S := P2MMultO.decField Aval) (liftPt (S := P2MMultOR.decRing Aval) g)).ofConv := by
    rw [comp_liftPt, galF_restrictScalars, h2, WithConv.toConv_ofConv]
  have hσ : ∀ x, (liftPt (S := P2MMultO.decField Aval) (liftPt (S := P2MMultOR.decRing Aval) g)).ofConv x
      = galF Aval hτD ((liftPt (S := P2MMultO.decField Aval) (liftPt (S := P2MMultOR.decRing Aval) f)).ofConv x) := by
    intro x
    rw [← h3]
    rfl

  have htorsS : ∀ μ : ↥(P2MMultSFacade.KNF q Aval H M e he_add W), μ ^ N = 1 := by
    intro μ
    apply Subtype.ext
    obtain ⟨κ, hκ⟩ := liftPt_surjective (K := P2MMultOR.decRing Aval) (S := P2MMultO.decField Aval)
      (μ : P2MMultSFacade.PtsF q Aval H)
    obtain ⟨φ, rfl⟩ := liftPt_surjective (K := GaloisRep.ratLocalizedAt q) (S := P2MMultOR.decRing Aval) κ
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, ← hκ, ← liftPt_pow, ← liftPt_pow, htors, liftPt_one, liftPt_one]

  have hfix : ∀ ψ : P2MMultE.ptsE h, P2MMultE.galE h (galF Aval hτD) ψ = ψ :=
    fun ψ => (P2MMultE.galE_eq_self_iff h (galF Aval hτD) ψ).mpr (hEND τ hτ ψ)

  have key := P2MMultE.pow_of_galE_fixed h hev
    (P2MMultE.submonoid_mul_comm_of_isCocomm _) N hN0 htorsS (galF Aval hτD) (n τ)
    (galF_hn Aval hτD (hn τ)) hfix ⟨_, hνf⟩ ⟨_, hνg⟩ hσ

  have key' := congrArg Subtype.val key
  rw [SubmonoidClass.coe_pow] at key'
  change liftPt (S := P2MMultO.decField Aval) (liftPt (S := P2MMultOR.decRing Aval) g)
    = liftPt (S := P2MMultO.decField Aval) (liftPt (S := P2MMultOR.decRing Aval) f) ^ n τ at key'
  rw [← liftPt_pow, ← liftPt_pow] at key'
  exact liftPt_injective (liftPt_injective key')

end P2MMultFinal
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

end P13_HDUAL
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

section P9_FINAL

set_option autoImplicit false
set_option maxHeartbeats 25600000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

namespace P2MMultFinal

open WithConv
open scoped TensorProduct

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem mult_main
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J)
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) f g,
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q)
    (m : ℕ) (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ)
    (htors : ∀ x : ↥M, q ^ m • x = 0)
    (M' : AddSubgroup J) (hM' : M' ≤ M)
    (r : ℕ) (step : Fin (r + 1) → AddSubgroup J) (hstep0 : step 0 = ⊥) (hstepr : step (Fin.last r) = M')
    (hmono : ∀ i : Fin r, step i.castSucc ≤ step i.succ)
    (hstab : ∀ i, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ step i, σ • x ∈ step i)
    (hcard : ∀ i : Fin r, Nat.card (↥(step i.succ) ⧸ (step i.castSucc).addSubgroupOf (step i.succ)) = q)
    (hadm : ∀ i : Fin r,
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ step i.succ, σ • x - x ∈ step i.castSucc) ∨
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ step i.succ, σ • x - n σ • x ∈ step i.castSucc))
    (K : AddSubgroup J) (hKM : K ≤ M)
    (hK : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
      ((e f : ↥M) : J) ∈ K ↔
        ∀ h : H, Aq.valuation (f h
          - algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) :
    ModularCurve.MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n (K ⊓ M') := by
  classical

  haveI hF1 : Fact (((q : ℕ) : ℚ̄) ∈ Aq.nonunits) := ⟨hAq⟩
  haveI hF2 : Fact (∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : ℚ̄) ∈ Aq.nonunits) := ⟨⟨q, Fact.out, hAq⟩⟩
  haveI : Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)) := P2MMultEv.finite_pts q H

  have htorsH : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄), f ^ (q ^ m) = 1 :=
    P2MMultEv.pow_eq_one_of_torsion q H M e he_add m htors

  have hlab : ∀ x : J, x ∈ M → ∃ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄), ((e f : ↥M) : J) = x :=
    fun x hx => ⟨e.symm ⟨x, hx⟩, by rw [Equiv.apply_symm_apply]⟩

  have hKst : ∀ σ : Gal, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ K, σ • x ∈ K := by
    intro σ hσ x hx
    obtain ⟨f, rfl⟩ := hlab x (hKM hx)
    rw [← he_act σ f (toConv (((σ : ℚ̄ →ₐ[ℚ] ℚ̄).restrictScalars (GaloisRep.ratLocalizedAt q)).comp f.ofConv))
      (fun _ => rfl), hK]
    intro h
    have h1 := (hK f).mp hx h
    show Aq.valuation (σ (f h) - algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ (Coalgebra.counit h)) < 1
    rw [← P2MMultEv.gal_algebraMap q σ (Coalgebra.counit h), ← map_sub]
    exact P2MMultEv.valuation_lt_one_of_mem_decomposition Aq hσ h1

  let K' : Fin (r + 1) → AddSubgroup J := fun i => K ⊓ step i
  have hK'st : ∀ i, ∀ σ : Gal, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ K' i, σ • x ∈ K' i :=
    fun i σ hσ x hx => ⟨hKst σ hσ x hx.1, hstab i σ x hx.2⟩

  have hev0 := P2MMultSFacade.evGen_bijective_PtsF q Aq H (P2MMultEv.evGen_bijective q H)
  have hstabE : ∀ (N : AddSubgroup J), (∀ σ : Gal, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N) →
      ∀ σ : Gal, σ ∈ Aq.decompositionSubgroup ℚ → ∀ ν ∈ P2MMultSFacade.KNF q Aq H M e he_add N,
        ∃ ν' ∈ P2MMultSFacade.KNF q Aq H M e he_add N, ∀ a, (ofConv ν') a = σ ((ofConv ν) a) :=
    fun N hN σ hσ ν hν => ⟨toConv (((P2MMultSAdapt.galF Aq hσ) : ℚ̄ →ₐ[P2MMultO.decField Aq] ℚ̄).comp (ofConv ν)),
      P2MMultSFacade.KNF_stab q Aq H M e he_add he_act N hN hσ (P2MMultSAdapt.galF Aq hσ) (fun _ => rfl) hν,
      fun _ => rfl⟩
  have hT6 : ∀ (N : AddSubgroup J), (∀ σ : Gal, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N) →
      Function.Bijective (HopfAlgebra.evalQuot (P2MMultSFacade.KNF q Aq H M e he_add N)) ∧
      ∀ x : HopfAlgebra.pointQuot (P2MMultSFacade.KNF q Aq H M e he_add N) ⊗[↥(IntermediateField.fixedField (Aq.decompositionSubgroup ℚ))]
          HopfAlgebra.pointQuot (P2MMultSFacade.KNF q Aq H M e he_add N),
        (∀ ν ν' (hν : ν ∈ HopfAlgebra.ptSet (P2MMultSFacade.KNF q Aq H M e he_add N))
            (hν' : ν' ∈ HopfAlgebra.ptSet (P2MMultSFacade.KNF q Aq H M e he_add N)),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet (P2MMultSFacade.KNF q Aq H M e he_add N)) ν ν' hν hν' x = 0) → x = 0 :=
    fun N hN => HopfAlgebra.evalQuot_bijective_of_forall_exists_comp_eq (Aq.decompositionSubgroup ℚ)
      (↥(P2MMultO.decField Aq) ⊗[P2MMultOR.decRing Aq] P2MMultSFacade.GG q Aq H) hev0
      (P2MMultSFacade.KNF q Aq H M e he_add N) (hstabE N hN)
  have hevN : ∀ (N : AddSubgroup J), (∀ σ : Gal, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N) →
      Function.Bijective (P2MMultE.evQ (P2MMultSFacade.KNF q Aq H M e he_add N)) :=
    fun N hN => (hT6 N hN).1
  have hIP : ∀ (N : AddSubgroup J), (∀ σ : Gal, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N) →
      P2MMultE.IPtHyp (P2MMultSFacade.KNF q Aq H M e he_add N) :=
    fun N hN => P2MMultE.IPtHyp.of_sep_inv (hT6 N hN).2
      (fun ν hν => P2MMultSFacade.KNF_inv q Aq H M e he_add N ν hν)
  have hstab' : ∀ (N : AddSubgroup J), (∀ σ : Gal, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N) →
      ∀ (σ : Gal) (hσ : σ ∈ Aq.decompositionSubgroup ℚ), ∀ ν ∈ P2MMultSFacade.KNF q Aq H M e he_add N,
        toConv (((P2MMultSAdapt.galF Aq hσ) : ℚ̄ →ₐ[P2MMultO.decField Aq] ℚ̄).comp (ofConv ν))
          ∈ P2MMultSFacade.KNF q Aq H M e he_add N :=
    fun N hN σ hσ ν hν => P2MMultSFacade.KNF_stab q Aq H M e he_add he_act N hN hσ (P2MMultSAdapt.galF Aq hσ)
      (fun _ => rfl) hν

  have hRI : ∀ i : Fin (r + 1), RedInj q Aq H (hIP (K' i) (hK'st i)) := by
    refine Fin.induction ?_ ?_
    · refine inj_base q Aq H M e he_add (K' 0) ?_ (hIP _ (hK'st _)) (hevN _ (hK'st _))
      intro x hx
      have h0 : x ∈ step 0 := hx.2
      rw [hstep0] at h0
      exact AddSubgroup.mem_bot.mp h0
    · intro i IH
      have hχ : ∀ σ : Gal, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ K' i.succ, σ • x - n σ • x ∈ K' i.castSucc := by
        intro σ hσ x hx
        have hxK : σ • x - n σ • x ∈ K := K.sub_mem (hKst σ hσ x hx.1) (K.nsmul_mem hx.1 _)
        rcases hadm i with htriv | hchi
        ·
          obtain ⟨f, hf⟩ := hlab x (hKM hx.1)
          have hx' : x ∈ K' i.castSucc := by
            rw [← hf]
            refine GaloisRep.label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf q hq2 H M e he_add he_act
              Aq hAq m (K' i.castSucc) (hK'st _) f ?_ ?_ (htorsH f)
            · exact (hK f).mp (hf ▸ hx.1)
            · intro σ' hσ'
              refine ⟨K.sub_mem (hKst σ' hσ' _ (hf ▸ hx.1)) (hf ▸ hx.1), ?_⟩
              rw [hf]
              exact htriv σ' x hx.2
          exact ⟨hxK, (step i.castSucc).sub_mem (hK'st _ σ hσ x hx').2 (AddSubgroup.nsmul_mem _ hx'.2 _)⟩
        · exact ⟨hxK, hchi σ x hx.2⟩
      exact inj_step q Aq H M e he_add hq2 m htorsH n hn (K' i.castSucc) (K' i.succ)
        (fun x hx => ⟨hx.1, hmono i hx.2⟩) (hIP _ (hK'st _)) (hIP _ (hK'st _)) (hevN _ (hK'st _)) (hevN _ (hK'st _))
        (chiS_of_chi q Aq H M e he_add he_act m htorsH n (K' i.castSucc) (K' i.succ) hχ)
        (hstab' (K' i.succ) (hK'st _)) IH

  subst hstepr
  have hEND := end_of_redInj q Aq H M e he_add (K' (Fin.last r)) (hIP _ (hK'st _)) (hRI (Fin.last r))
  have hdual := hdual_of_END q Aq H M e he_add he_act (K' (Fin.last r)) (hK'st _) (q ^ m)
    (pow_pos (Fact.out : q.Prime).pos m) htorsH n hn (hIP _ (hK'st _)) (hevN _ (hK'st _)) hEND
  exact P2MMultE.multiplicativeTypeNat_of_forall_twist_eq_pow (fun σ : Gal => (σ : ℚ̄ → ℚ̄)) M e he_add he_act
    (fun σ f => ⟨toConv (((σ : ℚ̄ →ₐ[ℚ] ℚ̄).restrictScalars (GaloisRep.ratLocalizedAt q)).comp f.ofConv), fun _ => rfl⟩)
    (Aq.inertiaSubgroupIn ℚ) n (K' (Fin.last r)) (fun x hx => hKM hx.1) hdual

end P2MMultFinal
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"
end P9_FINAL
p2m_reactivate "P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultO P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultOR P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSAdapt P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultSFacade P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultE P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.P2MMultEv"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J)
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) f g,
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q)
    (m : ℕ) (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ)
    (htors : ∀ x : ↥M, q ^ m • x = 0)
    (M' : AddSubgroup J) (hM' : M' ≤ M)
    (r : ℕ) (step : Fin (r + 1) → AddSubgroup J) (hstep0 : step 0 = ⊥) (hstepr : step (Fin.last r) = M')
    (hmono : ∀ i : Fin r, step i.castSucc ≤ step i.succ)
    (hstab : ∀ i, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ step i, σ • x ∈ step i)
    (hcard : ∀ i : Fin r, Nat.card (↥(step i.succ) ⧸ (step i.castSucc).addSubgroupOf (step i.succ)) = q)
    (hadm : ∀ i : Fin r,
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ step i.succ, σ • x - x ∈ step i.castSucc) ∨
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ step i.succ, σ • x - n σ • x ∈ step i.castSucc))
    (K : AddSubgroup J) (hKM : K ≤ M)
    (hK : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
      ((e f : ↥M) : J) ∈ K ↔
        ∀ h : H, Aq.valuation (f h
          - algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) :
    ModularCurve.MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n (K ⊓ M') :=
  P2MMultFinal.mult_main q hq2 H M e he_add he_act Aq hAq m n hn htors M' hM' r step hstep0 hstepr hmono hstab hcard hadm K hKM hK

end S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain
end P2MW
export P2MW.S_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain (solution)
