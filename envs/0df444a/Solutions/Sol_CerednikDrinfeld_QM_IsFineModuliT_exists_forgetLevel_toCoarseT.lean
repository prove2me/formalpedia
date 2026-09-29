-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuliT.exists_forgetLevel_toCoarseT
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c2d1b784-21a2-5532-b82e-44c291fe6926

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_over_of_forall_schemeHomOver
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_exists_forgetLevel_toCoarseT
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (hsep : IsSeparated fM) (hfin : ∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (ℓ : HeckeTower.AwayPrime r rbar)

    (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
          u.1.ExtraLevel (ℓ.1 : ℕ) → SchemeHomOver s fMℓ)
    (hMℓ : IsFineModuliT Λ N n (ℓ.1 : ℕ) Mℓ fMℓ ptFℓ)
    (πℓ : Mℓ ⟶ M) (hπℓf : πℓ ≫ fM = fMℓ)
    (hπℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (C : u.1.ExtraLevel (ℓ.1 : ℕ)), (ptFℓ S s u C).1 ≫ πℓ = (ptF S s u).1) :
    ∃ (pℓ : Mℓ ⟶ 𝒴 ℓ) (hpℓg : pℓ ≫ g ℓ = fMℓ),
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (C : u.1.ExtraLevel (ℓ.1 : ℕ)), (ptFℓ S s u C).1 ≫ pℓ = (ptT ℓ S s ⟨u.1, C⟩).1 := by
  classical
  have hY := h𝒴 ℓ

  choose uOf COf hptOf using hMℓ.ptFℓ_surjective

  have isoPair : ∀ (S : Type) [CommRing S] (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
      (C : u.1.ExtraLevel (ℓ.1 : ℕ)) (C' : u'.1.ExtraLevel (ℓ.1 : ℕ)) (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
      FakeEllipticCurve.WithFullLevel.IsoTVia u u' C C' i hi →
      FakeEllipticCurve.WithExtraLevel.Iso (⟨u.1, C⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) ⟨u'.1, C'⟩ := by
    intro S _ u u' C C' i hi hv
    exact ⟨i, hi, hv.1.1, hv.1.2.1, hv.1.2.2.1, hv.2⟩

  have hpt_wd : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel (ℓ.1 : ℕ)) (C' : u'.1.ExtraLevel (ℓ.1 : ℕ)),
      ptFℓ S s u C = ptFℓ S s u' C' → ptT ℓ S s ⟨u.1, C⟩ = ptT ℓ S s ⟨u'.1, C'⟩ := by
    intro S _ s u u' C C' h
    obtain ⟨i, hi, hv⟩ := hMℓ.ptFℓ_injective S s u u' C C' h
    exact hY.ptT_iso S s _ _ (isoPair S u u' C C' i hi hv)

  let e : ∀ (T : Type) [CommRing T] (φ : 𝒪 →+* T),
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) fMℓ → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (g ℓ) :=
    fun T _ φ x => ptT ℓ T (Spec.map (CommRingCat.ofHom φ)) ⟨(uOf T (Spec.map (CommRingCat.ofHom φ)) x).1, COf T (Spec.map (CommRingCat.ofHom φ)) x⟩
  have e_def : ∀ (T : Type) [CommRing T] (φ : 𝒪 →+* T) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) fMℓ),
      e T φ x = ptT ℓ T (Spec.map (CommRingCat.ofHom φ)) ⟨(uOf T (Spec.map (CommRingCat.ofHom φ)) x).1, COf T (Spec.map (CommRingCat.ofHom φ)) x⟩ := fun _ _ _ _ => rfl
  have e_spec : ∀ (T : Type) [CommRing T] (φ : 𝒪 →+* T) (u : FakeEllipticCurve.WithFullLevel Λ N n T) (C : u.1.ExtraLevel (ℓ.1 : ℕ)),
      e T φ (ptFℓ T (Spec.map (CommRingCat.ofHom φ)) u C) = ptT ℓ T (Spec.map (CommRingCat.ofHom φ)) ⟨u.1, C⟩ := by
    intro T _ φ u C
    rw [e_def]
    exact hpt_wd T (Spec.map (CommRingCat.ofHom φ)) _ _ _ _ (hptOf T (Spec.map (CommRingCat.ofHom φ)) (ptFℓ T (Spec.map (CommRingCat.ofHom φ)) u C))

  have e_nat : ∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : 𝒪 →+* T) (ψ : T →+* T')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) fMℓ),
      (e T' (ψ.comp φ) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by
          rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩).1 =
        Spec.map (CommRingCat.ofHom ψ) ≫ (e T φ x).1 := by
    intro T T' _ _ φ ψ x
    have hs : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

    set u := uOf T (Spec.map (CommRingCat.ofHom φ)) x with hudef
    set C := COf T (Spec.map (CommRingCat.ofHom φ)) x with hCdef
    have hptx : ptFℓ T (Spec.map (CommRingCat.ofHom φ)) u C = x := hptOf T (Spec.map (CommRingCat.ofHom φ)) x
    obtain ⟨u₂, g₂, hg₂, Hmul, HΛ, Hlev⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isPullback (Λ := Λ) (N := N) ψ
        (⟨u.1, C⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) T)
    have hvia : FakeEllipticCurve.IsPullbackVia ψ u.1 u₂.1 g₂ := ⟨hg₂, Hmul, HΛ, fun t' P => (Hlev t' P).1⟩

    obtain ⟨P', hP'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia n ψ u.1 u₂.1 g₂ hvia u.2
    let w' : FakeEllipticCurve.WithFullLevel Λ N n T' := ⟨u₂.1, P'⟩
    have hptw' : (ptFℓ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ))) w' u₂.2).1 = Spec.map (CommRingCat.ofHom ψ) ≫ x.1 := by
      rw [hMℓ.ptFℓ_pullback T T' ψ (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (ψ.comp φ))) hs u w' C u₂.2 g₂ hvia hP' (fun t' P h => (Hlev t' P).2 h), hptx]
    have hpteq : ptFℓ T' (Spec.map (CommRingCat.ofHom (ψ.comp φ))) w' u₂.2 =
        ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩ :=
      Subtype.ext hptw'
    rw [← hpteq, e_spec]
    have hpair : (⟨w'.1, u₂.2⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) T') = u₂ := rfl
    rw [hpair, hY.ptT_pullback T T' ψ (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (ψ.comp φ))) hs ⟨u.1, C⟩ u₂ ⟨g₂, hg₂, Hmul, HΛ, Hlev⟩, e_def]

  obtain ⟨pℓ, hpℓg, hpℓpt, -⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_hom_over_of_forall_schemeHomOver fMℓ (g ℓ) e e_nat
  refine ⟨pℓ, hpℓg, ?_⟩
  intro S _ s u C
  obtain ⟨φ', rfl⟩ := Spec.map_surjective s
  have h := hpℓpt S φ'.hom (ptFℓ S _ u C)
  rw [e_spec] at h
  exact h

end S_CerednikDrinfeld_QM_IsFineModuliT_exists_forgetLevel_toCoarseT
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_exists_forgetLevel_toCoarseT (solution)
