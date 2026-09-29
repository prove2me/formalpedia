-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuliT.exists_iso_of_isFineModuliT
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2d35cc58-798e-58f3-b148-3ece43c2281c

import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_over_of_forall_schemeHomOver
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_exists_iso_of_isFineModuliT
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace FinSurjTUniq

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n ℓ : ℕ} {B : Type} [CommRing B]

private theorem _root_.FinSurjTUniq.hom_ext
    {Mℓ : Scheme.{0}} {πMℓ : Mℓ ⟶ Spec (CommRingCat.of B)}
    {ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ}
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ πMℓ ptFℓ) {Y : Scheme.{0}} (g₁ g₂ : Mℓ ⟶ Y)
    (h : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ), (ptFℓ S s u C).1 ≫ g₁ = (ptFℓ S s u C).1 ≫ g₂) :
    g₁ = g₂ := by
  refine Scheme.Cover.hom_ext Mℓ.affineCover g₁ g₂ fun j => ?_
  let R := Mℓ.affineOpenCover.X j
  obtain ⟨u, C, hu⟩ := hMℓ.ptFℓ_surjective ↑R (Mℓ.affineOpenCover.f j ≫ πMℓ) ⟨Mℓ.affineOpenCover.f j, rfl⟩
  have h1 : (ptFℓ ↑R (Mℓ.affineOpenCover.f j ≫ πMℓ) u C).1 = Mℓ.affineOpenCover.f j := by rw [hu]
  show Mℓ.affineOpenCover.f j ≫ g₁ = Mℓ.affineOpenCover.f j ≫ g₂
  rw [← h1]; exact h _ _ u C

p2m_export "FinSurjTUniq" "hom_ext"

theorem exists_hom
    {Mℓ : Scheme.{0}} {πMℓ : Mℓ ⟶ Spec (CommRingCat.of B)}
    {ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ}
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ πMℓ ptFℓ)
    {Mℓ' : Scheme.{0}} {πMℓ' : Mℓ' ⟶ Spec (CommRingCat.of B)}
    {ptFℓ' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ'}
    (hMℓ' : IsFineModuliT Λ N n ℓ Mℓ' πMℓ' ptFℓ') :
    ∃ Φ : Mℓ ⟶ Mℓ', Φ ≫ πMℓ' = πMℓ ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ), (ptFℓ S s u C).1 ≫ Φ = (ptFℓ' S s u C).1 := by
  classical

  choose uOf COf hptOf using hMℓ.ptFℓ_surjective
  have hpt_wd : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ),
      ptFℓ S s u C = ptFℓ S s u' C' → ptFℓ' S s u C = ptFℓ' S s u' C' := by
    intro S _ s u u' C C' h
    obtain ⟨i, hi, hv⟩ := hMℓ.ptFℓ_injective S s u u' C C' h
    exact hMℓ'.ptFℓ_iso S s u u' C C' i hi hv

  let e : ∀ (R : Type) [CommRing R] (φ : B →+* R),
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πMℓ → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πMℓ' :=
    fun R _ φ x => ptFℓ' R (Spec.map (CommRingCat.ofHom φ)) (uOf R (Spec.map (CommRingCat.ofHom φ)) x) (COf R (Spec.map (CommRingCat.ofHom φ)) x)
  have e_def : ∀ (R : Type) [CommRing R] (φ : B →+* R) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πMℓ),
      e R φ x = ptFℓ' R (Spec.map (CommRingCat.ofHom φ)) (uOf R (Spec.map (CommRingCat.ofHom φ)) x) (COf R (Spec.map (CommRingCat.ofHom φ)) x) :=
    fun _ _ _ _ => rfl
  have e_spec : ∀ (R : Type) [CommRing R] (φ : B →+* R) (u : FakeEllipticCurve.WithFullLevel Λ N n R) (C : u.1.ExtraLevel ℓ),
      e R φ (ptFℓ R (Spec.map (CommRingCat.ofHom φ)) u C) = ptFℓ' R (Spec.map (CommRingCat.ofHom φ)) u C := by
    intro R _ φ u C
    rw [e_def]
    exact hpt_wd R (Spec.map (CommRingCat.ofHom φ)) _ _ _ _
      (hptOf R (Spec.map (CommRingCat.ofHom φ)) (ptFℓ R (Spec.map (CommRingCat.ofHom φ)) u C))

  have e_nat : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : B →+* R) (ψ : R →+* R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πMℓ),
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
    obtain ⟨P', hP'⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia n ψ u.1 u₂.1 g₂ hvia u.2
    let w' : FakeEllipticCurve.WithFullLevel Λ N n R' := ⟨u₂.1, P'⟩
    have hptw' : (ptFℓ R' (Spec.map (CommRingCat.ofHom (ψ.comp φ))) w' u₂.2).1 = Spec.map (CommRingCat.ofHom ψ) ≫ x.1 := by
      rw [hMℓ.ptFℓ_pullback R R' ψ (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (ψ.comp φ))) hs u w' C u₂.2 g₂
        hvia hP' (fun t' P h => (Hlev t' P).2 h), hptx]
    have hpteq : ptFℓ R' (Spec.map (CommRingCat.ofHom (ψ.comp φ))) w' u₂.2 =
        ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩ :=
      Subtype.ext hptw'
    rw [← hpteq, e_spec,
      hMℓ'.ptFℓ_pullback R R' ψ (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (ψ.comp φ))) hs u w' C u₂.2 g₂
        hvia hP' (fun t' P h => (Hlev t' P).2 h), e_def]

  obtain ⟨Φ, hΦπ, hΦpt, -⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver πMℓ πMℓ' e e_nat
  refine ⟨Φ, hΦπ, ?_⟩
  intro S _ s u C
  obtain ⟨φ', rfl⟩ := Spec.map_surjective s
  have h := hΦpt S φ'.hom (ptFℓ S _ u C)
  rw [e_spec] at h
  exact h

end FinSurjTUniq

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N n ℓ : ℕ) {B : Type} [CommRing B]
    {Mℓ : Scheme.{0}} {πMℓ : Mℓ ⟶ Spec (CommRingCat.of B)}
    {ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ}
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ πMℓ ptFℓ)
    {Mℓ' : Scheme.{0}} {πMℓ' : Mℓ' ⟶ Spec (CommRingCat.of B)}
    {ptFℓ' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ'}
    (hMℓ' : IsFineModuliT Λ N n ℓ Mℓ' πMℓ' ptFℓ') :
    ∃ e : Mℓ ≅ Mℓ', e.hom ≫ πMℓ' = πMℓ ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ),
        (ptFℓ S s u C).1 ≫ e.hom = (ptFℓ' S s u C).1) ∧
      (∀ g : Mℓ ⟶ Mℓ', g ≫ πMℓ' = πMℓ →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ),
          (ptFℓ S s u C).1 ≫ g = (ptFℓ' S s u C).1) → g = e.hom) := by
  obtain ⟨g, hgπ, hg⟩ := FinSurjTUniq.exists_hom hMℓ hMℓ'
  obtain ⟨g', -, hg'⟩ := FinSurjTUniq.exists_hom hMℓ' hMℓ
  have h1 : g ≫ g' = 𝟙 Mℓ := FinSurjTUniq.hom_ext hMℓ _ _ fun S _ s u C => by
    rw [← Category.assoc, hg S s u C, hg' S s u C, Category.comp_id]
  have h2 : g' ≫ g = 𝟙 Mℓ' := FinSurjTUniq.hom_ext hMℓ' _ _ fun S _ s u C => by
    rw [← Category.assoc, hg' S s u C, hg S s u C, Category.comp_id]
  refine ⟨⟨g, g', h1, h2⟩, hgπ, fun S _ s u C => hg S s u C, ?_⟩
  intro k _ hk
  exact FinSurjTUniq.hom_ext hMℓ _ _ fun S _ s u C => by rw [hk S s u C, hg S s u C]

end S_CerednikDrinfeld_QM_IsFineModuliT_exists_iso_of_isFineModuliT
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_exists_iso_of_isFineModuliT (solution)
