-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_galT_of_coarse_of_two_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fa83b6a5-a325-51e4-af72-e7f1ba404a73

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_hom_comp_eq_specMap_ringEquiv
import Theorems.Thm_AlgebraicCurve_SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_galT_of_coarse_of_two_mul_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

namespace GalTPack

abbrev Kb : Type := AlgebraicClosure ℚ

noncomputable abbrev sp (σ : Kb ≃ₐ[ℚ] Kb) : Spec (CommRingCat.of Kb) ⟶ Spec (CommRingCat.of Kb) :=
  Spec.map (CommRingCat.ofHom (σ : Kb →+* Kb))

theorem coe_ringEquiv_eq (σ : Kb ≃ₐ[ℚ] Kb) : ((σ : Kb ≃+* Kb) : Kb →+* Kb) = (σ : Kb →+* Kb) := rfl

theorem sp_mul (σ σ' : Kb ≃ₐ[ℚ] Kb) : sp σ ≫ sp σ' = sp (σ * σ') := by
  simp only [sp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem sp_one : sp 1 = 𝟙 _ := by
  simp only [sp]
  change Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem toRingEquiv_mul (σ σ' : Kb ≃ₐ[ℚ] Kb) : ((σ * σ') : Kb ≃+* Kb) = (σ : Kb ≃+* Kb) * (σ' : Kb ≃+* Kb) := by
  ext x; rfl

theorem toRingEquiv_one : ((1 : Kb ≃ₐ[ℚ] Kb) : Kb ≃+* Kb) = 1 := by
  ext x; rfl

end GalTPack

open GalTPack in
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
    ∃ galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ),
      (∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
    SemilinearAut.baseAut (galT ℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    ∃ (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)) (g : u.1.A ⟶ (repT ℓ P).1.A)
      (hg : CategoryTheory.IsPullback g u.1.f (repT ℓ P).1.f
        (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q Q' : SchemeHomOver t' u.1.f),
        (u.1.L.mul t' Q Q').1 ≫ g =
          ((repT ℓ P).1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, u.1.act x ≫ g = g ≫ (repT ℓ P).1.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t' u.1.f),
        (FactorsThrough u.1.lev Q → ∃ Q₀ : T ⟶ (repT ℓ P).1.C, Q₀ ≫ (repT ℓ P).1.lev = Q.1 ≫ g) ∧
        (FactorsThrough u.2.levK Q → ∃ Q₀ : T ⟶ (repT ℓ P).2.K, Q₀ ≫ (repT ℓ P).2.levK = Q.1 ≫ g)) ∧
      FakeEllipticCurve.WithExtraLevel.Iso u (repT ℓ (galT ℓ σ • P))) := by
  classical

  have key : ∀ ℓ : HeckeTower.AwayPrime q q',
      ∃ galTℓ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ),
        (∀ σ, SemilinearAut.baseAut (galTℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
          ∃ u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ),
            FakeEllipticCurve.WithExtraLevel.IsPullback (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (repT ℓ P) u ∧
            FakeEllipticCurve.WithExtraLevel.Iso u (repT ℓ (galTℓ σ • P)) := by
    intro ℓ
    haveI : IsIso (eℓ ℓ) := heℓiso ℓ

    have ptT_congr : ∀ (S : Type) [CommRing S] (s s' : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of Kb)) (hs : s = s')
        (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 = (ptT ℓ S s' u).1 := by
      intro S _ s s' hs u; subst hs; rfl

    have hT1 := fun σ : Kb ≃ₐ[ℚ] Kb =>
      CerednikDrinfeld.QM.IsCoarseModuliT.existsUnique_hom_comp_eq_specMap_ringEquiv Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ)
        (hcoT ℓ) (σ : Kb ≃+* Kb)
    choose h hh huniq using hT1

    have hg : ∀ σ, h σ ≫ g ℓ = g ℓ ≫ sp σ := fun σ => (hh σ).1
    have hpt : ∀ σ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of Kb))
        (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S (s ≫ sp σ) u).1 = (ptT ℓ S s u).1 ≫ h σ :=
      fun σ S _ s u => (hh σ).2 S s u

    have hmul : ∀ σ σ', h (σ * σ') = h σ ≫ h σ' := by
      intro σ σ'
      refine ((huniq (σ * σ') (h σ ≫ h σ') ⟨?_, ?_⟩)).symm
      · show (h σ ≫ h σ') ≫ g ℓ = g ℓ ≫ sp (σ * σ')
        rw [Category.assoc, hg σ', ← Category.assoc, hg σ, Category.assoc, sp_mul]
      · intro S _ s u
        show (ptT ℓ S (s ≫ sp (σ * σ')) u).1 = (ptT ℓ S s u).1 ≫ h σ ≫ h σ'
        rw [ptT_congr S (s ≫ sp (σ * σ')) ((s ≫ sp σ) ≫ sp σ') (by rw [Category.assoc, sp_mul]) u,
          hpt σ' S (s ≫ sp σ) u, hpt σ S s u, Category.assoc]
    have hone : h 1 = 𝟙 _ := by
      refine ((huniq 1 (𝟙 _) ⟨?_, ?_⟩)).symm
      · show 𝟙 _ ≫ g ℓ = g ℓ ≫ sp 1
        rw [sp_one]; simp
      · intro S _ s u
        show (ptT ℓ S (s ≫ sp 1) u).1 = (ptT ℓ S s u).1 ≫ 𝟙 _
        rw [Category.comp_id, ptT_congr S (s ≫ sp 1) s (by rw [sp_one, Category.comp_id]) u]
    have hiso : ∀ σ, IsIso (h σ) := fun σ =>
      ⟨⟨h σ⁻¹, by rw [← hmul, mul_inv_cancel, hone], by rw [← hmul, inv_mul_cancel, hone]⟩⟩

    let H : (Kb ≃ₐ[ℚ] Kb) → ((Mℓ ℓ).C ⟶ (Mℓ ℓ).C) := fun σ => eℓ ℓ ≫ h σ ≫ inv (eℓ ℓ)
    have hHiso : ∀ σ, IsIso (H σ) := fun σ => by haveI := hiso σ; dsimp only [H]; infer_instance
    have htoBase : inv (eℓ ℓ) ≫ (Mℓ ℓ).toBase = g ℓ := by rw [← heℓ ℓ]; simp
    have hH : ∀ σ, H σ ≫ (Mℓ ℓ).toBase = (Mℓ ℓ).toBase ≫ Spec.map (CommRingCat.ofHom ((σ : Kb ≃+* Kb) : Kb →+* Kb)) := by
      intro σ
      simp only [H, Category.assoc, htoBase, hg σ, coe_ringEquiv_eq]
      rw [← Category.assoc, heℓ ℓ]
    have hHmul : ∀ σ σ', H (σ * σ') = H σ ≫ H σ' := by
      intro σ σ'; simp only [H, hmul, Category.assoc, IsIso.inv_hom_id_assoc]
    have hHone : H 1 = 𝟙 _ := by simp only [H, hone, Category.id_comp, IsIso.hom_inv_id]

    have h78 := fun σ : Kb ≃ₐ[ℚ] Kb => by
      haveI := hHiso σ
      exact AlgebraicCurve.CurveModel.exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul (Mℓ ℓ)
        (σ : Kb ≃+* Kb) (H σ) (hH σ)
    choose G hGbase _hGgerm hGpt using h78

    have hinvBase : ∀ σ, inv (H σ) ≫ (Mℓ ℓ).toBase = (Mℓ ℓ).toBase ≫ sp σ⁻¹ := by
      intro σ
      haveI := hHiso σ
      rw [IsIso.inv_comp_eq, ← Category.assoc, hH σ, Category.assoc, coe_ringEquiv_eq]
      symm
      show (Mℓ ℓ).toBase ≫ (sp σ ≫ sp σ⁻¹) = (Mℓ ℓ).toBase
      rw [sp_mul, mul_inv_cancel, sp_one, Category.comp_id]
    let ysec : (Kb ≃ₐ[ℚ] Kb) → Place Kb (𝕋.F ℓ) →
        {p : Spec (CommRingCat.of Kb) ⟶ (Mℓ ℓ).C // p ≫ (Mℓ ℓ).toBase = 𝟙 _} := fun σ P =>
      ⟨sp σ ≫ ((Mℓ ℓ).pointEquivPlace.symm P).1 ≫ inv (H σ), by
        haveI := hHiso σ
        rw [Category.assoc, Category.assoc, hinvBase σ, ← Category.assoc ((Mℓ ℓ).pointEquivPlace.symm P).1,
          ((Mℓ ℓ).pointEquivPlace.symm P).2, Category.id_comp, sp_mul, mul_inv_cancel, sp_one]⟩
    have hGsmul : ∀ σ P, G σ • P = (Mℓ ℓ).pointEquivPlace (ysec σ P) := by
      intro σ P
      haveI := hHiso σ
      have := hGpt σ ((Mℓ ℓ).pointEquivPlace.symm P) (ysec σ P) (by
        show (sp σ ≫ ((Mℓ ℓ).pointEquivPlace.symm P).1 ≫ inv (H σ)) ≫ H σ = _
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, coe_ringEquiv_eq])
      rw [this, Equiv.apply_symm_apply]

    let galTℓ : (Kb ≃ₐ[ℚ] Kb) →* SemilinearAut Kb (𝕋.F ℓ) :=
      { toFun := G
        map_one' := by
          apply AlgebraicCurve.SemilinearAut.eq_of_baseAut_eq_of_forall_smul_place_eq
          · rw [hGbase, SemilinearAut.baseAut_one]; ext x; rfl
          · intro P
            rw [hGsmul, one_smul]
            conv_rhs => rw [← (Mℓ ℓ).pointEquivPlace.apply_symm_apply P]
            congr 1
            apply Subtype.ext
            show sp 1 ≫ ((Mℓ ℓ).pointEquivPlace.symm P).1 ≫ inv (H 1) = ((Mℓ ℓ).pointEquivPlace.symm P).1
            haveI := hHiso 1
            have : inv (H 1) = 𝟙 _ := by rw [IsIso.inv_eq_of_hom_inv_id]; rw [hHone]; simp
            rw [this, sp_one]; simp
        map_mul' := fun σ σ' => by
          apply AlgebraicCurve.SemilinearAut.eq_of_baseAut_eq_of_forall_smul_place_eq
          · rw [hGbase, SemilinearAut.baseAut_mul, hGbase, hGbase]; ext x; rfl
          · intro P
            rw [mul_smul, hGsmul, hGsmul, hGsmul]
            congr 1
            apply Subtype.ext
            show sp (σ * σ') ≫ ((Mℓ ℓ).pointEquivPlace.symm P).1 ≫ inv (H (σ * σ')) =
              sp σ ≫ ((Mℓ ℓ).pointEquivPlace.symm ((Mℓ ℓ).pointEquivPlace (ysec σ' P))).1 ≫ inv (H σ)
            rw [Equiv.symm_apply_apply]
            show sp (σ * σ') ≫ ((Mℓ ℓ).pointEquivPlace.symm P).1 ≫ inv (H (σ * σ')) =
              sp σ ≫ (sp σ' ≫ ((Mℓ ℓ).pointEquivPlace.symm P).1 ≫ inv (H σ')) ≫ inv (H σ)
            haveI := hHiso σ; haveI := hHiso σ'; haveI := hHiso (σ * σ')
            have : inv (H (σ * σ')) = inv (H σ') ≫ inv (H σ) := by
              rw [IsIso.inv_eq_of_hom_inv_id]; rw [hHmul]; simp
            rw [this, ← sp_mul]; simp only [Category.assoc] }
    refine ⟨galTℓ, fun σ => hGbase σ, ?_⟩

    intro σ P
    obtain ⟨u, hu⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isPullback
      (σ : Kb →+* Kb) (repT ℓ P)
    refine ⟨u, hu, ?_⟩
    apply (hcoT ℓ).ptT_injective Kb (𝟙 _) u (repT ℓ (galTℓ σ • P))
    apply Subtype.ext
    haveI := hiso σ; haveI := hHiso σ

    have h1 : (ptT ℓ Kb (sp σ) u).1 = sp σ ≫ (ptT ℓ Kb (𝟙 _) (repT ℓ P)).1 :=
      (hcoT ℓ).ptT_pullback Kb Kb (σ : Kb →+* Kb) (𝟙 _) (sp σ) (Category.comp_id _) (repT ℓ P) u hu
    have h2 : (ptT ℓ Kb (sp σ) u).1 = (ptT ℓ Kb (𝟙 _) u).1 ≫ h σ := by
      rw [ptT_congr Kb (sp σ) (𝟙 _ ≫ sp σ) (Category.id_comp _).symm u]; exact hpt σ Kb (𝟙 _) u
    have h3 : (ptT ℓ Kb (𝟙 _) u).1 = sp σ ≫ (ptT ℓ Kb (𝟙 _) (repT ℓ P)).1 ≫ inv (h σ) := by
      rw [← Category.assoc, ← h1, h2]; simp

    have h4 : (ptT ℓ Kb (𝟙 _) (repT ℓ (galTℓ σ • P))).1 = sp σ ≫ (ptT ℓ Kb (𝟙 _) (repT ℓ P)).1 ≫ inv (h σ) := by
      rw [ptT_repT, ptT_repT]
      show ((Mℓ ℓ).pointEquivPlace.symm (G σ • P)).1 ≫ eℓ ℓ = _
      rw [hGsmul, Equiv.symm_apply_apply]
      show (sp σ ≫ ((Mℓ ℓ).pointEquivPlace.symm P).1 ≫ inv (H σ)) ≫ eℓ ℓ = _
      have : inv (H σ) ≫ eℓ ℓ = eℓ ℓ ≫ inv (h σ) := by
        rw [IsIso.inv_comp_eq]
        simp only [H, Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id, Category.comp_id]
      simp only [Category.assoc, this]
    rw [h3, h4]
  choose galT hgalT using key
  exact ⟨galT, fun ℓ σ => (hgalT ℓ).1 σ, fun ℓ σ P => by
    obtain ⟨u, ⟨gA, hgA, hmul, hact, hlev⟩, hiso⟩ := (hgalT ℓ).2 σ P
    exact ⟨u, gA, hgA, hmul, hact, hlev, hiso⟩⟩

end S_CerednikDrinfeld_QM_exists_galT_of_coarse_of_two_mul_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_galT_of_coarse_of_two_mul_dvd (solution)
