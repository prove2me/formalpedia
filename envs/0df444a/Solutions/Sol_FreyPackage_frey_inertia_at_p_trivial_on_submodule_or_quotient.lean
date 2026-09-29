-- Prove2me | solution 1 for FreyPackage.frey_inertia_at_p_trivial_on_submodule_or_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/de4cdcd2-e5ae-5628-93a2-d7ae2bcaa0ec

import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped Pointwise

namespace ValuationSubring
p2m_export "ValuationSubring" "ext mem_nonunits_iff smul_mem_pointwise_smul mem_pointwise_smul_iff_inv_smul_mem decompositionSubgroup exists_algEquiv_smul_eq_of_liesOverPrime LiesOverPrime inertiaSubgroupIn"
p2m_open "ValuationSubring"

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def smulRingEquiv (τ : L ≃ₐ[K] L) (A : ValuationSubring L) : A ≃+* ↥(τ • A) where
  toFun a := ⟨τ • (a : L), smul_mem_pointwise_smul τ (a : L) A a.2⟩
  invFun b := ⟨τ⁻¹ • (b : L), mem_pointwise_smul_iff_inv_smul_mem.mp b.2⟩
  left_inv a := by ext; simp
  right_inv b := by ext; simp
  map_mul' a b := by ext; simp [smul_mul']
  map_add' a b := by ext; simp [smul_add]

@[scoped simp] lemma coe_smulRingEquiv_apply (τ : L ≃ₐ[K] L) (A : ValuationSubring L) (a : A) :
    ((smulRingEquiv τ A a : ↥(τ • A)) : L) = τ • (a : L) := rfl

@[scoped simp] lemma coe_smulRingEquiv_symm_apply (τ : L ≃ₐ[K] L) (A : ValuationSubring L)
    (b : ↥(τ • A)) : ((smulRingEquiv τ A).symm b : L) = τ⁻¹ • (b : L) := rfl

lemma map_mem_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) :
    e x ∈ IsLocalRing.maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff] at hx ⊢
  intro h
  apply hx
  simpa using h.map e.symm

theorem mem_inertiaSubgroupIn_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.inertiaSubgroupIn K ↔ ∃ h : σ ∈ A.decompositionSubgroup K,
      ∀ a : A, (⟨σ, h⟩ : A.decompositionSubgroup K) • a - a ∈ IsLocalRing.maximalIdeal A := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d.2, fun a => ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero,
      IsLocalRing.ResidueField.residue_smul]
    have hd' : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
        (IsLocalRing.ResidueField A) d = 1 := hd
    exact RingEquiv.congr_fun hd' (IsLocalRing.residue A a)
  · rintro ⟨h, hσ⟩
    refine ⟨⟨σ, h⟩, ?_, rfl⟩
    show MulSemiringAction.toRingAut (A.decompositionSubgroup K)
        (IsLocalRing.ResidueField A) ⟨σ, h⟩ = 1
    ext r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨σ, h⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact hσ a

theorem conj_mem_inertiaSubgroupIn {A : ValuationSubring L} {σ : L ≃ₐ[K] L} (τ : L ≃ₐ[K] L)
    (hσ : σ ∈ A.inertiaSubgroupIn K) : τ * σ * τ⁻¹ ∈ (τ • A).inertiaSubgroupIn K := by
  rw [mem_inertiaSubgroupIn_iff] at hσ ⊢
  obtain ⟨hD, hI⟩ := hσ
  have hD' : σ • A = A := hD
  have hD'' : (τ * σ * τ⁻¹) • (τ • A) = τ • A := by
    rw [mul_smul, mul_smul, inv_smul_smul, hD']
  refine ⟨hD'', fun b => ?_⟩
  set e := smulRingEquiv τ A with he
  have key : (⟨τ * σ * τ⁻¹, hD''⟩ : (τ • A).decompositionSubgroup K) • b - b =
      e ((⟨σ, hD⟩ : A.decompositionSubgroup K) • e.symm b - e.symm b) := by
    rw [map_sub, RingEquiv.apply_symm_apply]
    congr 1
  rw [key]
  exact map_mem_maximalIdeal_of_ringEquiv e (hI _)

theorem inv_mul_mul_mem_inertiaSubgroupIn {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (τ : L ≃ₐ[K] L) (hσ : σ ∈ (τ • A).inertiaSubgroupIn K) :
    τ⁻¹ * σ * τ ∈ A.inertiaSubgroupIn K := by
  have := conj_mem_inertiaSubgroupIn τ⁻¹ hσ
  rwa [inv_inv, inv_smul_smul] at this

end ValuationSubring
p2m_reactivate "P2MW.S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.ValuationSubring"

theorem solution (P : FreyPackage) (N : Submodule (ZMod P.p) (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime P.p → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ N, σ • x = x) ∨ (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime P.p → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, σ • x - x ∈ N) := by
  by_cases hex : ∃ A₀ : ValuationSubring (AlgebraicClosure ℚ), A₀.LiesOverPrime P.p
  swap
  ·
    left
    intro A hA
    exact absurd ⟨A, hA⟩ hex
  obtain ⟨A₀, hA₀⟩ := hex
  rcases P.frey_inertia_at_p_trivial_on_submodule_or_quotient_at N hN hbot htop A₀ hA₀ with
    hfix | hcofix
  · left
    intro A hA σ hσ x hx
    obtain ⟨τ, rfl⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime P.pp A₀ A hA₀ hA
    have h1 := hfix _ (ValuationSubring.inv_mul_mul_mem_inertiaSubgroupIn τ hσ) (τ⁻¹ • x)
      (hN τ⁻¹ x hx)

    have h2 := congrArg (fun y => τ • y) h1
    simpa [mul_smul] using h2
  · right
    intro A hA σ hσ x
    obtain ⟨τ, rfl⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime P.pp A₀ A hA₀ hA
    have h1 := hcofix _ (ValuationSubring.inv_mul_mul_mem_inertiaSubgroupIn τ hσ) (τ⁻¹ • x)
    have h2 := hN τ _ h1
    simpa [mul_smul, smul_sub] using h2

end S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient
end P2MW
export P2MW.S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient (solution)
