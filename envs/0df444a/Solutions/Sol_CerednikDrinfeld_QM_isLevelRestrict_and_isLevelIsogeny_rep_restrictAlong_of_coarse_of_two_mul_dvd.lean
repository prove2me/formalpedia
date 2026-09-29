-- Prove2me | solution 1 for CerednikDrinfeld.QM.isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/34683884-81a4-51b7-bd43-50f3d2252a0e

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isLevelIsogeny
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd.CerednikDrinfeld.QM"
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.WithExtraLevel QM.FakeEllipticCurve HeckeTower.AwayPrime HeckeTower.TowerData QM.FakeEllipticCurve.WithExtraLevel.exists_isLevelIsogeny"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithExtraLevel FakeEllipticCurve.IsLevelRestrict FakeEllipticCurve.IsLevelIsogeny mapPt mapPt_coe FakeEllipticCurve FakeEllipticCurve.Iso FakeEllipticCurve.IsPullback IsCoarseModuli IsCoarseModuliT FakeEllipticCurve.WithExtraLevel.exists_isLevelIsogeny"
namespace RestrictReduce
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

theorem isLevelIsogeny_of_iso_right
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (d d' : FakeEllipticCurve Λ N S)
    (h : FakeEllipticCurve.IsLevelIsogeny ℓ u d) (hdd' : FakeEllipticCurve.Iso d d') :
    FakeEllipticCurve.IsLevelIsogeny ℓ u d' := by
  obtain ⟨e, he, hmul_e, hact_e, hlev_e⟩ := hdd'
  obtain ⟨φ, hφ, ψ, hψ, hmulφ, hmulψ, hactφ, hactψ, hℓ, hker, hlev⟩ := h
  have he' : e.inv ≫ d.f = d'.f := by rw [Iso.inv_comp_eq, he]
  have hφ' : (φ ≫ e.hom) ≫ d'.f = u.1.f := by rw [Category.assoc, he, hφ]
  have hψ' : (e.inv ≫ ψ) ≫ u.1.f = d'.f := by rw [Category.assoc, hψ, he']

  have hmap : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt (φ ≫ e.hom) hφ' P = mapPt e.hom he (mapPt φ hφ P) :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.assoc])
  have hmap' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t d'.f),
      mapPt (e.inv ≫ ψ) hψ' P = mapPt ψ hψ (mapPt e.inv he' P) :=
    fun t P => Subtype.ext (by simp only [mapPt_coe, Category.assoc])

  have hmul_einv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t d'.f),
      mapPt e.inv he' (d'.L.mul t P Q) = d.L.mul t (mapPt e.inv he' P) (mapPt e.inv he' Q) := by
    intro T t P Q
    have hP : mapPt e.hom he (mapPt e.inv he' P) = P :=
      Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have hQ : mapPt e.hom he (mapPt e.inv he' Q) = Q :=
      Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have h := hmul_e t (mapPt e.inv he' P) (mapPt e.inv he' Q)
    rw [hP, hQ] at h
    apply Subtype.ext
    have h1 := congrArg (fun R : SchemeHomOver t d'.f => R.1 ≫ e.inv) h
    simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h1
    simpa only [mapPt_coe] using h1.symm

  have hinj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t d.f),
      mapPt e.hom he P = mapPt e.hom he Q → P = Q := by
    intro T t P Q hPQ
    have h1 := congrArg (fun R : SchemeHomOver t d'.f => R.1 ≫ e.inv) hPQ
    simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h1
    exact Subtype.ext h1

  have hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)),
      mapPt e.hom he (d.L.one t) = d'.L.one t := by
    intro T t
    have hy : d'.L.mul t (mapPt e.hom he (d.L.one t)) (mapPt e.hom he (d.L.one t)) = mapPt e.hom he (d.L.one t) := by
      have h := hmul_e t (d.L.one t) (d.L.one t)
      rw [d.L.one_mul] at h
      exact h.symm
    symm
    calc d'.L.one t
        = d'.L.mul t (d'.L.inv t (mapPt e.hom he (d.L.one t))) (mapPt e.hom he (d.L.one t)) :=
          (d'.L.inv_mul_cancel t _).symm
      _ = d'.L.mul t (d'.L.inv t (mapPt e.hom he (d.L.one t)))
            (d'.L.mul t (mapPt e.hom he (d.L.one t)) (mapPt e.hom he (d.L.one t))) := by rw [hy]
      _ = d'.L.mul t (d'.L.mul t (d'.L.inv t (mapPt e.hom he (d.L.one t))) (mapPt e.hom he (d.L.one t)))
            (mapPt e.hom he (d.L.one t)) := (d'.L.mul_assoc t _ _ _).symm
      _ = mapPt e.hom he (d.L.one t) := by rw [d'.L.inv_mul_cancel, d'.L.one_mul]
  refine ⟨φ ≫ e.hom, hφ', e.inv ≫ ψ, hψ', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [hmap, hmap, hmap, hmulφ, hmul_e]
  · intro T t P Q
    rw [hmap', hmap', hmap', hmul_einv, hmulψ]
  · intro x
    rw [← Category.assoc, hactφ, Category.assoc, hact_e, ← Category.assoc]
  · intro x
    have hx : d'.act x ≫ e.inv = e.inv ≫ d.act x := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, hact_e]
    rw [← Category.assoc, hx, Category.assoc, hactψ, ← Category.assoc]
  · intro hℓΛ
    obtain ⟨h1, h2⟩ := hℓ hℓΛ
    constructor
    · rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact h1
    · rw [Category.assoc, ← Category.assoc ψ, h2, hact_e, Iso.inv_hom_id_assoc]
  · intro T t P
    rw [hmap, ← hker]
    constructor
    · intro hP
      exact hinj t _ _ (hP.trans (hone t).symm)
    · intro hP
      rw [hP, hone]
  · intro T t P hP
    rw [hmap]
    exact (hlev_e t _).1 (hlev t P hP)

end CerednikDrinfeld.QM.RestrictReduce

theorem pt_fst_congr {B : Type} [CommRing B] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {X : Scheme.{0}} {πX : X ⟶ Spec (CommRingCat.of B)}
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    {S : Type} [CommRing S] {s s' : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)} (h : s = s') (E : FakeEllipticCurve Λ N S) :
    (pt S s E).1 = (pt S s' E).1 := by
  subst h; rfl

theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (hgal_base : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), SemilinearAut.baseAut (gal σ) = (σ : (AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)))

    (hgal_pt : ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (P : Place (AlgebraicClosure ℚ) Fbar),
      (𝔐.pointEquivPlace.symm (gal σ • P)).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar =
        Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫
          ((𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar))
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (pt𝒳 : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (hco : IsCoarseModuli Λ N 𝒳 f pt𝒳)
    (g𝒳 : 𝒳 ⟶ CategoryTheory.Limits.pullback πX sbar) [IsIso g𝒳]
    (hg𝒳 : g𝒳 ≫ CategoryTheory.Limits.pullback.snd πX sbar = f)
    (hg𝒳pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (E : FakeEllipticCurve Λ N S),
      (pt𝒳 S s E).1 ≫ g𝒳 ≫ CategoryTheory.Limits.pullback.fst πX sbar = (pt S (s ≫ sbar) E).1)
    (𝒴 : HeckeTower.AwayPrime q q' → Scheme.{0})
    (g : ∀ ℓ, 𝒴 ℓ ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (hcoT : ∀ ℓ, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (d₀ d₁ : ∀ ℓ, 𝒴 ℓ ⟶ 𝒳)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 ≫ d₀ ℓ = (pt𝒳 S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime q q') (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT ℓ S s u).1 ≫ d₁ ℓ = (pt𝒳 S s d).1)
    (rep : Place (AlgebraicClosure ℚ) Fbar → FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (pt_rep : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
      (pt _ sbar (rep P)).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar)
    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (Mℓ : ∀ ℓ : HeckeTower.AwayPrime q q', AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (eℓ : ∀ ℓ : HeckeTower.AwayPrime q q', (Mℓ ℓ).C ⟶ 𝒴 ℓ) (heℓiso : ∀ ℓ, IsIso (eℓ ℓ))
    (heℓ : ∀ ℓ, eℓ ℓ ≫ g ℓ = (Mℓ ℓ).toBase)

    (hφpt : ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
      (𝔐.pointEquivPlace.symm (R.restrictAlong (𝕋.φ (ℓ, i)) (𝕋.integral (ℓ, i)))).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar =
        ((Mℓ ℓ).pointEquivPlace.symm R).1 ≫ eℓ ℓ ≫ (if i = 0 then d₀ ℓ else d₁ ℓ) ≫ g𝒳 ≫ CategoryTheory.Limits.pullback.fst πX sbar)
    (repT : ∀ ℓ : HeckeTower.AwayPrime q q',
      Place (AlgebraicClosure ℚ) (𝕋.F ℓ) → FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ))
    (ptT_repT : ∀ (ℓ : HeckeTower.AwayPrime q q') (R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
      (ptT ℓ _ (𝟙 _) (repT ℓ R)).1 = ((Mℓ ℓ).pointEquivPlace.symm R).1 ≫ eℓ ℓ)
 :
    (∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.IsLevelRestrict (repT ℓ P) (rep (P.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0))))) ∧
    (∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) (repT ℓ P) (rep (P.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1))))) := by

  have key : ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (R : Place (AlgebraicClosure ℚ) (𝕋.F ℓ))
      (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      (ptT ℓ _ (𝟙 _) (repT ℓ R)).1 ≫ (if i = 0 then d₀ ℓ else d₁ ℓ) = (pt𝒳 _ (𝟙 _) E).1 →
      (pt _ sbar E).1 = (pt _ sbar (rep (R.restrictAlong (𝕋.φ (ℓ, i)) (𝕋.integral (ℓ, i))))).1 := by
    intro ℓ i R E hE
    rw [pt_rep, hφpt ℓ i R, ← reassoc_of% (ptT_repT ℓ R)]
    rw [pt_fst_congr pt (Category.id_comp sbar).symm E, ← hg𝒳pt _ (𝟙 _) E, ← hE]
    simp only [Category.assoc]
  constructor
  · intro ℓ R
    show FakeEllipticCurve.Iso (repT ℓ R).1 _
    apply pt_injective (AlgebraicClosure ℚ) sbar
    apply Subtype.ext
    exact key ℓ 0 R (repT ℓ R).1 (by rw [if_pos rfl]; exact hd₀ ℓ _ (𝟙 _) (repT ℓ R))
  · intro ℓ R
    have hℓ0 : (((ℓ.1 : ℕ) : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast ℓ.1.prop.ne_zero
    have hN0 : ((N : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
    haveI : Fact (ℓ.1 : ℕ).Prime := ⟨ℓ.1.prop⟩
    obtain ⟨d, hd⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isLevelIsogeny hqq' hB Λ hΛ (ℓ.1 : ℕ) ℓ.2.1 ℓ.2.2
      (AlgebraicClosure ℚ) hℓ0 hN0 (repT ℓ R)
    have hiso : FakeEllipticCurve.Iso d (rep (R.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1)))) := by
      apply pt_injective (AlgebraicClosure ℚ) sbar
      apply Subtype.ext
      exact key ℓ 1 R d (by rw [if_neg (by decide)]; exact hd₁ ℓ _ (𝟙 _) (repT ℓ R) d hd)
    exact CerednikDrinfeld.QM.RestrictReduce.isLevelIsogeny_of_iso_right (ℓ.1 : ℕ) _ d _ hd hiso

end S_CerednikDrinfeld_QM_isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_isLevelRestrict_and_isLevelIsogeny_rep_restrictAlong_of_coarse_of_two_mul_dvd (solution)
