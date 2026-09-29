-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_iso_pullback_equivariant_of_isLevelTwistAction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/0f036311-bcc5-5867-9ba2-443e6079db47

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_of_isFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isTwist_and_fst_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_isTwist_of_isTwist_of_sub_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_iso_pullback_equivariant_of_isLevelTwistAction
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

open CategoryTheory.Limits

namespace Law3FMB

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {B : Type} [CommRing B]

theorem hom_ext_ptF
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF) {Y : Scheme.{0}} (g₁ g₂ : M ⟶ Y)
    (h : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N m S), (ptF S s u).1 ≫ g₁ = (ptF S s u).1 ≫ g₂) : g₁ = g₂ := by
  refine Scheme.Cover.hom_ext M.affineCover g₁ g₂ fun j => ?_
  let R := M.affineOpenCover.X j
  obtain ⟨u, hu⟩ := hM.ptF_surjective ↑R (M.affineOpenCover.f j ≫ πM) ⟨M.affineOpenCover.f j, rfl⟩
  have h1 : (ptF ↑R (M.affineOpenCover.f j ≫ πM) u).1 = M.affineOpenCover.f j := by rw [hu]
  show M.affineOpenCover.f j ≫ g₁ = M.affineOpenCover.f j ≫ g₂
  rw [← h1]; exact h _ _ u

theorem label_mul_inv
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ) (g g' : G)
    (hgg' : g * g' = 1) :
    ∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  obtain ⟨y₁, h₁⟩ := hρ.label_mul g g'
  obtain ⟨y₀, h₀⟩ := hρ.label_one
  rw [hgg'] at h₁
  refine ⟨y₀ - y₁, ?_⟩
  rw [Submodule.coe_sub, smul_sub, ← h₀, ← h₁, sub_sub_sub_cancel_left]

end Law3FMB

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ) [NeZero N] (hm : 3 ≤ m)
    {B₀ 𝒪 : Type} [CommRing B₀] [CommRing 𝒪] (i : B₀ →+* 𝒪) (hi : Flat (Spec.map (CommRingCat.ofHom i)))
    (hN : IsUnit ((N : ℕ) : B₀)) (hm' : IsUnit ((m : ℕ) : B₀))

    {M₀ : Scheme.{0}} {πM₀ : M₀ ⟶ Spec (CommRingCat.of B₀)}
    {ptF₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM₀}
    (hM₀ : IsFineModuli Λ N m M₀ πM₀ ptF₀)
    {G₀ : Type} [Group G₀] [Finite G₀] {ρ₀ : G₀ →* Aut M₀} {χ₀ : G₀ → ↥Λ} (hρ₀ : IsLevelTwistAction Λ N m M₀ πM₀ ptF₀ G₀ ρ₀ χ₀)
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)

    (H : Type) [Group H] [Finite H] (φ₀ : H →* G₀) (hφ₀ : Function.Injective φ₀) (φ : H →* G) (hφ : Function.Injective φ)
    (hlabel : ∀ h : H, ∃ y : ↥Λ, (χ₀ (φ₀ h) : ℍ[ℚ, a, b]) - (χ (φ h) : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ e : M ⟶ Limits.pullback πM₀ (Spec.map (CommRingCat.ofHom i)),
      IsIso e ∧ e ≫ Limits.pullback.snd πM₀ (Spec.map (CommRingCat.ofHom i)) = πM ∧
      (∀ h : H, (ρ (φ h)).hom ≫ e =
        e ≫ Limits.pullback.lift (Limits.pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i)) ≫ (ρ₀ (φ₀ h)).hom)
              (Limits.pullback.snd πM₀ (Spec.map (CommRingCat.ofHom i)))
              (by rw [Category.assoc, hρ₀.over_base, Limits.pullback.condition])) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N m S),
        (ptF S s u).1 ≫ e ≫ Limits.pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i)) =
          (ptF₀ S (s ≫ Spec.map (CommRingCat.ofHom i)) u).1) := by
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.1
  set ι := Spec.map (CommRingCat.ofHom i) with hι
  have hpb : IsPullback (pullback.fst πM₀ ι) (pullback.snd πM₀ ι) πM₀ ι := IsPullback.of_hasPullback _ _
  obtain ⟨ptP, hP, hptP⟩ :=
    CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_of_isPullback i hM₀ (pullback.snd πM₀ ι) (pullback.fst πM₀ ι) hpb
  obtain ⟨e, heπ, he, -⟩ := CerednikDrinfeld.QM.IsFineModuli.exists_iso_of_isFineModuli Λ N m hM hP
  refine ⟨e.hom, inferInstance, heπ, ?_, ?_⟩
  · intro h
    apply Law3FMB.hom_ext_ptF hM
    intro S _ s u

    obtain ⟨u', htw', -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isTwist_and_fst_eq hΛo u
      (χ (φ h)) (χ (φ h⁻¹)) (Law3FMB.label_mul_inv hρ _ _ (by rw [← map_mul, mul_inv_cancel, map_one]))
      (Law3FMB.label_mul_inv hρ _ _ (by rw [← map_mul, inv_mul_cancel, map_one]))
    obtain ⟨u'', htw'', -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isTwist_and_fst_eq hΛo u
      (χ₀ (φ₀ h)) (χ₀ (φ₀ h⁻¹)) (Law3FMB.label_mul_inv hρ₀ _ _ (by rw [← map_mul, mul_inv_cancel, map_one]))
      (Law3FMB.label_mul_inv hρ₀ _ _ (by rw [← map_mul, inv_mul_cancel, map_one]))
    have hIso : FakeEllipticCurve.WithFullLevel.Iso u'' u' :=
      CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_isTwist_of_isTwist_of_sub_eq_smul hΛo u u'' u'
        (χ₀ (φ₀ h)) (χ (φ h)) htw'' htw' (hlabel h)

    rw [← Category.assoc, ← hρ.twist (φ h) S s u u' htw', he S s u', ← Category.assoc, he S s u,
      ← hP.ptF_iso S s u'' u' hIso]

    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hptP S s u, hptP S s u'']
      exact hρ₀.twist (φ₀ h) S (s ≫ ι) u u'' htw''
    · rw [Category.assoc, pullback.lift_snd]
      exact ((ptP S s u'').2).trans ((ptP S s u).2).symm
  · intro S _ s u
    rw [← Category.assoc, he S s u, hptP S s u]

end S_CerednikDrinfeld_QM_IsFineModuli_exists_iso_pullback_equivariant_of_isLevelTwistAction
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_iso_pullback_equivariant_of_isLevelTwistAction (solution)
