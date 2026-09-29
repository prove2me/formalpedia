-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/31c8a24c-4ec8-5dce-9faa-1d67845e8cc6

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace P3RigPullback

universe u

variable {R : Type u} [CommRing R] {A A' A'' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}

theorem mapPt_mapPt (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    (h : (φ ≫ ψ) ≫ f'' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) h P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]

variable (L : GoodReductionJacobian.RelativeGroupLaw R f)

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

end P3RigPullback

open P3RigPullback in
theorem solution
    {r N : ℕ}
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B B' : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
    (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B) (E' : FakeEllipticCurve Λ N B') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E E' g)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    ∃ ρ' : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) E',
      FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ρ ρ' := by

  let φb : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B' ⧸ Ideal.span {algebraMap 𝒪 B' π}) := (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (φ : B →+* B')
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (φ : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from φ.commutes π]
            exact Ideal.subset_span rfl)))))
  have hφb : φb.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (φ : B →+* B') := Ideal.quotientMap_comp_mk _
  obtain ⟨hsqg, gmul, gact, glev⟩ := hg
  obtain ⟨hsqb, bmul, bact, blev⟩ := ρ.isPullback_Eb
  obtain ⟨hsqA, Amul, Aact, Alev⟩ := ρ.isPullback_Ab
  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := ρ.isIsogenyPair

  obtain ⟨Eb', ub, hub, ubmul, ubact, ublev, ublev'⟩ := FakeEllipticCurve.exists_isPullback_levelIff φb ρ.Eb
  obtain ⟨Ab', uA, huA, uAmul, uAact, uAlev, uAlev'⟩ := FakeEllipticCurve.exists_isPullback_levelIff φb ρ.Ab

  have ptext : ∀ {S₁ : Type} [CommRing S₁] {X Y Z : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of S₁)} {gg : X ⟶ Y} {fY : Y ⟶ Z}
      {s : Spec (CommRingCat.of S₁) ⟶ Z} (hsq : CategoryTheory.IsPullback gg fX fY s)
      {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S₁)} (P Q : SchemeHomOver t fX), P.1 ≫ gg = Q.1 ≫ gg → P = Q := by
    intro S₁ _ X Y Z fX gg fY s hsq T t P Q h
    exact Subtype.ext (hsq.hom_ext h (by rw [P.2, Q.2]))

  have hSpec : Spec.map (CommRingCat.ofHom φb) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B' π}))) ≫ Spec.map (CommRingCat.ofHom (φ : B →+* B')) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hφb]
  have wgb : (ub ≫ ρ.gb) ≫ E.f =
      (Eb'.f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B' π})))) ≫ Spec.map (CommRingCat.ofHom (φ : B →+* B')) := by
    rw [Category.assoc, hsqb.w, ← Category.assoc, hub.w, Category.assoc, hSpec, Category.assoc]
  let gb' : Eb'.A ⟶ E'.A := hsqg.lift (ub ≫ ρ.gb) _ wgb
  have hgb'₁ : gb' ≫ g = ub ≫ ρ.gb := hsqg.lift_fst _ _ _
  have hgb'₂ : gb' ≫ E'.f = Eb'.f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B' π}))) := hsqg.lift_snd _ _ _
  have hsqb' : CategoryTheory.IsPullback gb' Eb'.f E'.f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B' π})))) := by
    have big : CategoryTheory.IsPullback (ub ≫ ρ.gb) Eb'.f E.f
        (Spec.map (CommRingCat.ofHom φb) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})))) :=
      hub.paste_horiz hsqb
    rw [← hgb'₁, hSpec] at big
    exact big.of_right hgb'₂ hsqg

  let φn : Eb'.A ⟶ Ab'.A := huA.lift (ub ≫ ρ.φ) Eb'.f (by rw [Category.assoc, hφo]; exact hub.w)
  have hφn₁ : φn ≫ uA = ub ≫ ρ.φ := huA.lift_fst _ _ _
  have hφn₂ : φn ≫ Ab'.f = Eb'.f := huA.lift_snd _ _ _
  let φn' : Ab'.A ⟶ Eb'.A := hub.lift (uA ≫ ρ.φ') Ab'.f (by rw [Category.assoc, hφ'o]; exact huA.w)
  have hφn'₁ : φn' ≫ ub = uA ≫ ρ.φ' := hub.lift_fst _ _ _
  have hφn'₂ : φn' ≫ Eb'.f = Ab'.f := hub.lift_snd _ _ _

  have φn_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B' ⧸ Ideal.span {algebraMap 𝒪 B' π}))) (P Q : SchemeHomOver t Eb'.f),
      mapPt φn hφn₂ (Eb'.L.mul t P Q) = Ab'.L.mul t (mapPt φn hφn₂ P) (mapPt φn hφn₂ Q) := by
    intro T t P Q
    apply ptext huA
    rw [mapPt_coe, Category.assoc, hφn₁, ← Category.assoc, ubmul, uAmul]
    have := congrArg Subtype.val (hφmul (t ≫ Spec.map (CommRingCat.ofHom φb))
      ⟨P.1 ≫ ub, by rw [Category.assoc, hub.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ ub, by rw [Category.assoc, hub.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr ρ.Ab.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hφn₁])
      (by simp only [mapPt_coe, Category.assoc, hφn₁])
  have φn'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B' ⧸ Ideal.span {algebraMap 𝒪 B' π}))) (P Q : SchemeHomOver t Ab'.f),
      mapPt φn' hφn'₂ (Ab'.L.mul t P Q) = Eb'.L.mul t (mapPt φn' hφn'₂ P) (mapPt φn' hφn'₂ Q) := by
    intro T t P Q
    apply ptext hub
    rw [mapPt_coe, Category.assoc, hφn'₁, ← Category.assoc, uAmul, ubmul]
    have := congrArg Subtype.val (hφ'mul (t ≫ Spec.map (CommRingCat.ofHom φb))
      ⟨P.1 ≫ uA, by rw [Category.assoc, huA.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ uA, by rw [Category.assoc, huA.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr ρ.Eb.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hφn'₁])
      (by simp only [mapPt_coe, Category.assoc, hφn'₁])

  have φn_act : ∀ x : ↥Λ, Eb'.act x ≫ φn = φn ≫ Ab'.act x := by
    intro x
    apply huA.hom_ext
    · rw [Category.assoc, hφn₁, ← Category.assoc, ubact, Category.assoc, hφlin, Category.assoc, uAact, ← Category.assoc φn uA, hφn₁,
        Category.assoc]
    · rw [Category.assoc, hφn₂, Eb'.act_over, Category.assoc, Ab'.act_over, hφn₂]
  have φn'_act : ∀ x : ↥Λ, Ab'.act x ≫ φn' = φn' ≫ Eb'.act x := by
    intro x
    apply hub.hom_ext
    · rw [Category.assoc, hφn'₁, ← Category.assoc, uAact, Category.assoc, hφ'lin, Category.assoc, ubact, ← Category.assoc φn' ub, hφn'₁,
        Category.assoc]
    · rw [Category.assoc, hφn'₂, Ab'.act_over, Category.assoc, Eb'.act_over, hφn'₂]

  have φn_deg : ∀ hm : (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φn ≫ φn' = Eb'.act ⟨_, hm⟩ ∧ φn' ≫ φn = Ab'.act ⟨_, hm⟩ := by
    intro hm
    obtain ⟨h1, h2⟩ := hdeg hm
    constructor
    · apply hub.hom_ext
      · rw [Category.assoc, hφn'₁, ← Category.assoc, hφn₁, Category.assoc, h1, ubact]
      · rw [Category.assoc, hφn'₂, hφn₂, Eb'.act_over]
    · apply huA.hom_ext
      · rw [Category.assoc, hφn₁, ← Category.assoc, hφn'₁, Category.assoc, h2, uAact]
      · rw [Category.assoc, hφn₂, hφn'₂, Ab'.act_over]

  have φn_lev : FakeEllipticCurve.PreservesLevel Eb' Ab' φn hφn₂ := by
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := ublev t P hP
    have hQ := ρ.preservesLevel (t ≫ Spec.map (CommRingCat.ofHom φb))
      ⟨P.1 ≫ ub, by rw [Category.assoc, hub.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
    apply uAlev'
    obtain ⟨Q₀, hQ₀⟩ := hQ
    exact ⟨Q₀, by rw [hQ₀]; simp only [mapPt_coe, Category.assoc, hφn₁]⟩

  have hres : FakeEllipticCurve.Rigidification.residueLeg π (φ.comp ψ) = φb.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp [FakeEllipticCurve.Rigidification.residueLeg, Ideal.quotientMap_mk, φb]
  have hAb' : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (φ.comp ψ)) A₀ Ab' (uA ≫ ρ.gA) := by
    rw [hres]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [CommRingCat.ofHom_comp, Spec.map_comp]
      exact huA.paste_horiz hsqA
    · intro T t' P Q
      rw [← Category.assoc, uAmul, Amul]
      exact mul_val_congr A₀.L (by rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]) _ _ _ _
        (by simp only [Category.assoc]) (by simp only [Category.assoc])
    · intro x
      rw [← Category.assoc, uAact, Category.assoc, Aact, Category.assoc]
    · intro T t' P hP
      obtain ⟨P₀, hP₀⟩ := uAlev t' P hP
      obtain ⟨P₁, hP₁⟩ := Alev (t' ≫ Spec.map (CommRingCat.ofHom φb))
        ⟨P.1 ≫ uA, by rw [Category.assoc, huA.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
      exact ⟨P₁, by rw [hP₁, Category.assoc]⟩
  have hEb' : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B' π})) E' Eb' gb' := by
    refine ⟨hsqb', ?_, ?_, ?_⟩
    · intro T t' P Q
      apply hsqg.hom_ext
      · rw [Category.assoc, hgb'₁, ← Category.assoc, ubmul, bmul, gmul]
        exact mul_val_congr E.L (by simp only [Category.assoc, hSpec]) _ _ _ _
          (by simp only [Category.assoc, hgb'₁]) (by simp only [Category.assoc, hgb'₁])
      · rw [Category.assoc, hgb'₂, ← Category.assoc, (Eb'.L.mul t' P Q).2, (E'.L.mul _ _ _).2]
    · intro x
      apply hsqg.hom_ext
      · rw [Category.assoc, hgb'₁, ← Category.assoc, ubact, Category.assoc, bact, Category.assoc, gact, ← Category.assoc gb' g, hgb'₁,
          Category.assoc]
      · rw [Category.assoc, Category.assoc, E'.act_over, hgb'₂, ← Category.assoc, Eb'.act_over]
    · intro T t' P hP
      obtain ⟨P₀, hP₀⟩ := ublev t' P hP
      obtain ⟨P₁, hP₁⟩ := blev (t' ≫ Spec.map (CommRingCat.ofHom φb))
        ⟨P.1 ≫ ub, by rw [Category.assoc, hub.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
      have hfac := CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback (φ : B →+* B') E E' g hsqg gmul glev
        (t' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B' π}))))
        ⟨P.1 ≫ gb', by rw [Category.assoc, hgb'₂, ← Category.assoc, P.2]⟩
        ⟨P₁, by rw [hP₁]; simp only [Category.assoc, hgb'₁]⟩
      exact hfac
  refine ⟨{ Eb := Eb', gb := gb', isPullback_Eb := hEb', Ab := Ab', gA := uA ≫ ρ.gA, isPullback_Ab := hAb', d := ρ.d,
            φ := φn, φ' := φn', φ_over := hφn₂,
            isIsogenyPair := ⟨hφn₂, hφn'₂, φn_hom, φn'_hom, φn_act, φn'_act, φn_deg⟩, preservesLevel := φn_lev },
          ub, uA, ⟨hub, ubmul, ubact, ublev⟩, hgb'₁.symm, ⟨huA, uAmul, uAact, uAlev⟩, rfl, rfl, hφn₁.symm⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_of_isPullbackVia (solution)
