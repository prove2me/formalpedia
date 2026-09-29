-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuliT.existsUnique_hom_ptFT_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/96989ead-cc78-5eb3-b14e-1214b63397ee

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_over_of_forall_schemeHomOver
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_existsUnique_hom_ptFT_comp_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n ℓ : ℕ} {𝒪 : Type} [CommRing 𝒪]
    {Mℓ : Scheme.{0}} {fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪)}
    {ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      u.1.ExtraLevel ℓ → SchemeHomOver s fMℓ}
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ fMℓ ptFℓ)
    (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of 𝒪))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πT)
    (hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
      FakeEllipticCurve.WithExtraLevel.Iso u u' → pt' S s u = pt' S s u')
    (hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
      FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (pt' S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).1) :
    ∃! Φ : Mℓ ⟶ T, Φ ≫ πT = fMℓ ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ), (pt' S s ⟨u.1, C⟩).1 = (ptFℓ S s u C).1 ≫ Φ := by
  classical

  choose uOf COf hptOf using hMℓ.ptFℓ_surjective
  have isoPair : ∀ (S : Type) [CommRing S] (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
      (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ) (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
      FakeEllipticCurve.WithFullLevel.IsoTVia u u' C C' i hi →
      FakeEllipticCurve.WithExtraLevel.Iso (⟨u.1, C⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) ⟨u'.1, C'⟩ := by
    intro S _ u u' C C' i hi hv
    exact ⟨i, hi, hv.1.1, hv.1.2.1, hv.1.2.2.1, hv.2⟩
  have hpt_wd : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ),
      ptFℓ S s u C = ptFℓ S s u' C' → pt' S s ⟨u.1, C⟩ = pt' S s ⟨u'.1, C'⟩ := by
    intro S _ s u u' C C' h
    obtain ⟨i, hi, hv⟩ := hMℓ.ptFℓ_injective S s u u' C C' h
    exact hiso S s _ _ (isoPair S u u' C C' i hi hv)

  let e : ∀ (R : Type) [CommRing R] (φ : 𝒪 →+* R),
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) fMℓ → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πT :=
    fun R _ φ x => pt' R (Spec.map (CommRingCat.ofHom φ)) ⟨(uOf R (Spec.map (CommRingCat.ofHom φ)) x).1, COf R (Spec.map (CommRingCat.ofHom φ)) x⟩
  have e_def : ∀ (R : Type) [CommRing R] (φ : 𝒪 →+* R) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) fMℓ),
      e R φ x = pt' R (Spec.map (CommRingCat.ofHom φ)) ⟨(uOf R (Spec.map (CommRingCat.ofHom φ)) x).1, COf R (Spec.map (CommRingCat.ofHom φ)) x⟩ := fun _ _ _ _ => rfl
  have e_spec : ∀ (R : Type) [CommRing R] (φ : 𝒪 →+* R) (u : FakeEllipticCurve.WithFullLevel Λ N n R) (C : u.1.ExtraLevel ℓ),
      e R φ (ptFℓ R (Spec.map (CommRingCat.ofHom φ)) u C) = pt' R (Spec.map (CommRingCat.ofHom φ)) ⟨u.1, C⟩ := by
    intro R _ φ u C
    rw [e_def]
    exact hpt_wd R (Spec.map (CommRingCat.ofHom φ)) _ _ _ _ (hptOf R (Spec.map (CommRingCat.ofHom φ)) (ptFℓ R (Spec.map (CommRingCat.ofHom φ)) u C))

  have e_nat : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : 𝒪 →+* R) (ψ : R →+* R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) fMℓ),
      (e R' (ψ.comp φ) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by
          rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩).1 =
        Spec.map (CommRingCat.ofHom ψ) ≫ (e R φ x).1 := by
    intro R R' _ _ φ ψ x
    have hs : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    set u := uOf R (Spec.map (CommRingCat.ofHom φ)) x with hudef
    set C := COf R (Spec.map (CommRingCat.ofHom φ)) x with hCdef
    have hptx : ptFℓ R (Spec.map (CommRingCat.ofHom φ)) u C = x := hptOf R (Spec.map (CommRingCat.ofHom φ)) x
    obtain ⟨u₂, g₂, hg₂, Hmul, HΛ, Hlev⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isPullback (Λ := Λ) (N := N) ψ
        (⟨u.1, C⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ R)
    have hvia : FakeEllipticCurve.IsPullbackVia ψ u.1 u₂.1 g₂ := ⟨hg₂, Hmul, HΛ, fun t' P => (Hlev t' P).1⟩
    obtain ⟨P', hP'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia n ψ u.1 u₂.1 g₂ hvia u.2
    let w' : FakeEllipticCurve.WithFullLevel Λ N n R' := ⟨u₂.1, P'⟩
    have hptw' : (ptFℓ R' (Spec.map (CommRingCat.ofHom (ψ.comp φ))) w' u₂.2).1 = Spec.map (CommRingCat.ofHom ψ) ≫ x.1 := by
      rw [hMℓ.ptFℓ_pullback R R' ψ (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (ψ.comp φ))) hs u w' C u₂.2 g₂ hvia hP' (fun t' P h => (Hlev t' P).2 h), hptx]
    have hpteq : ptFℓ R' (Spec.map (CommRingCat.ofHom (ψ.comp φ))) w' u₂.2 =
        ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩ :=
      Subtype.ext hptw'
    rw [← hpteq, e_spec]
    have hpair : (⟨w'.1, u₂.2⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ R') = u₂ := rfl
    rw [hpair, hpb R R' ψ (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (ψ.comp φ))) hs ⟨u.1, C⟩ u₂ ⟨g₂, hg₂, Hmul, HΛ, Hlev⟩, e_def]

  obtain ⟨Φ, hΦπ, hΦpt, hΦuniq⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver fMℓ πT e e_nat
  have hchar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ), (pt' S s ⟨u.1, C⟩).1 = (ptFℓ S s u C).1 ≫ Φ := by
    intro S _ s u C
    obtain ⟨φ', rfl⟩ := Spec.map_surjective s
    have h := hΦpt S φ'.hom (ptFℓ S _ u C)
    rw [e_spec] at h
    exact h.symm
  refine ⟨Φ, ⟨hΦπ, hchar⟩, ?_⟩

  rintro Φ' ⟨-, hΦ'⟩
  apply hΦuniq Φ'
  intro R _ φ x
  have hx := hptOf R (Spec.map (CommRingCat.ofHom φ)) x
  rw [e_def, hΦ' R (Spec.map (CommRingCat.ofHom φ)) _ _, hx]

end S_CerednikDrinfeld_QM_IsFineModuliT_existsUnique_hom_ptFT_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_existsUnique_hom_ptFT_comp_eq (solution)
