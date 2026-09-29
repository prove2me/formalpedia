-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4c01b9aa-b012-5724-820b-866ee49bcdf8

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian CerednikDrinfeld.QM"
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S' S : Type} [CommRing S'] [CommRing S] (ρ : S' →+* S) (hN : IsUnit ((N : ℕ) : S))
    (E : FakeEllipticCurve Λ N S')
    (E₁ : FakeEllipticCurve Λ N S) (g₁ : E₁.A ⟶ E.A) (h₁ : FakeEllipticCurve.IsPullbackVia ρ E E₁ g₁)
    (E₂ : FakeEllipticCurve Λ N S) (g₂ : E₂.A ⟶ E.A) (h₂ : FakeEllipticCurve.IsPullbackVia ρ E E₂ g₂) :
    ∃ h : E₂.A ⟶ E₁.A, h ≫ g₁ = g₂ ∧ h ≫ E₁.f = E₂.f ∧ FakeEllipticCurve.IsPullbackVia (RingHom.id S) E₁ E₂ h := by
  classical
  obtain ⟨sq₁, hmul₁, hact₁, hlev₁⟩ := h₁
  obtain ⟨sq₂, hmul₂, hact₂, hlev₂⟩ := h₂

  let h : E₂.A ⟶ E₁.A := sq₁.lift g₂ E₂.f sq₂.w
  have hg : h ≫ g₁ = g₂ := sq₁.lift_fst _ _ _
  have hf : h ≫ E₁.f = E₂.f := sq₁.lift_snd _ _ _
  let h' : E₁.A ⟶ E₂.A := sq₂.lift g₁ E₁.f sq₁.w
  have hg' : h' ≫ g₂ = g₁ := sq₂.lift_fst _ _ _
  have hf' : h' ≫ E₂.f = E₁.f := sq₂.lift_snd _ _ _
  have hh' : h ≫ h' = 𝟙 _ :=
    sq₂.hom_ext (by rw [Category.assoc, hg', hg, Category.id_comp]) (by rw [Category.assoc, hf', hf, Category.id_comp])
  have h'h : h' ≫ h = 𝟙 _ :=
    sq₁.hom_ext (by rw [Category.assoc, hg, hg', Category.id_comp]) (by rw [Category.assoc, hf, hf', Category.id_comp])
  haveI : IsIso h := ⟨⟨h', hh', h'h⟩⟩
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 (Spec (CommRingCat.of S)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]

  have reindex : ∀ {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
      {T : Scheme.{0}} (t₁ t₂ : T ⟶ Spec (CommRingCat.of R)) (e : t₁ = t₂)
      (X Y : SchemeHomOver t₁ f) (X' Y' : SchemeHomOver t₂ f), X'.1 = X.1 → Y'.1 = Y.1 →
      (L.mul t₂ X' Y').1 = (L.mul t₁ X Y).1 := by
    intro R _ A f L T t₁ t₂ e X Y X' Y' hX hY
    subst e
    have : X' = X := Subtype.ext hX
    subst this
    have : Y' = Y := Subtype.ext hY
    subst this
    rfl

  have Φmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t' E₂.f),
      (E₂.L.mul t' P Q).1 ≫ h =
        (E₁.L.mul t' ⟨P.1 ≫ h, by rw [Category.assoc, hf]; exact P.2⟩ ⟨Q.1 ≫ h, by rw [Category.assoc, hf]; exact Q.2⟩).1 := by
    intro T t' P Q
    apply sq₁.hom_ext
    · rw [Category.assoc, hg, hmul₂ t' P Q, hmul₁ t']
      apply reindex E.L _ _ rfl
      · change P.1 ≫ g₂ = (P.1 ≫ h) ≫ g₁
        rw [Category.assoc, hg]
      · change Q.1 ≫ g₂ = (Q.1 ≫ h) ≫ g₁
        rw [Category.assoc, hg]
    · have e2 : ((E₂.L.mul t' P Q).1 ≫ h) ≫ E₁.f = t' := by
        rw [Category.assoc, hf]; exact (E₂.L.mul t' P Q).2
      rw [e2, (E₁.L.mul t' _ _).2]

  let Φ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S)), SchemeHomOver t' E₂.f → SchemeHomOver t' E₁.f :=
    fun t' P => ⟨P.1 ≫ h, by rw [Category.assoc, hf]; exact P.2⟩
  have Φ_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t' E₂.f),
      Φ t' (E₂.L.mul t' P Q) = E₁.L.mul t' (Φ t' P) (Φ t' Q) := by
    intro T t' P Q
    exact Subtype.ext (Φmul t' P Q)
  have eq_one_of_mul_self : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (X : SchemeHomOver t E₁.f),
      X = E₁.L.mul t X X → X = E₁.L.one t := by
    intro T t X hX
    calc X = E₁.L.mul t (E₁.L.inv t X) (E₁.L.mul t X X) := by
            rw [← E₁.L.mul_assoc, E₁.L.inv_mul_cancel, E₁.L.one_mul]
      _ = E₁.L.mul t (E₁.L.inv t X) X := by rw [← hX]
      _ = E₁.L.one t := E₁.L.inv_mul_cancel t X
  have Φ_one : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S)), Φ t' (E₂.L.one t') = E₁.L.one t' := by
    intro T t'
    apply eq_one_of_mul_self
    have := Φ_mul t' (E₂.L.one t') (E₂.L.one t')
    rwa [E₂.L.one_mul] at this
  have Φ_nsmul : ∀ (n : ℕ) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t' E₂.f),
      Φ t' (nsmulPt E₂.L t' n P) = nsmulPt E₁.L t' n (Φ t' P) := by
    intro n
    induction n with
    | zero => intro T t' P; exact Φ_one t'
    | succ n ih =>
      intro T t' P
      show Φ t' (E₂.L.mul t' (nsmulPt E₂.L t' n P) P) = E₁.L.mul t' (nsmulPt E₁.L t' n (Φ t' P)) (Φ t' P)
      rw [Φ_mul, ih]

  have hgeom : ∀ (k : Type) [Field k] (sk : S →+* k),
      geomPoint k sk ≫ Spec.map (CommRingCat.ofHom ρ) = geomPoint k (sk.comp ρ) := by
    intro k _ sk
    simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hNk : ∀ (k : Type) [Field k] (sk : S →+* k), (N : k) ≠ 0 := by
    intro k _ sk
    have := hN.map sk
    rw [map_natCast] at this
    exact this.ne_zero

  obtain ⟨-, crit₁⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.etale_lev_and_forall_factorsThrough_iff_of_isUnit E₁ hN

  have geomlev : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
      (Q : SchemeHomOver (geomPoint k sk) E₂.f), FactorsThrough E₂.lev Q →
        FactorsThrough E₁.lev (Φ (geomPoint k sk) Q) := by
    intro k _ _ sk Q hQ
    haveI : NeZero N := ⟨by rintro rfl; exact hNk k sk (by simp)⟩

    let C₁ := {R : SchemeHomOver (geomPoint k sk) E₁.f // FactorsThrough E₁.lev R}
    let CE := {R : SchemeHomOver (geomPoint k (sk.comp ρ)) E.f // FactorsThrough E.lev R}
    obtain ⟨e₁, -⟩ := E₁.lev_fibre k sk (hNk k sk)
    obtain ⟨eE, -⟩ := E.lev_fibre k (sk.comp ρ) (by
      have := (hN.map sk).map (RingHom.id k)
      simpa using hNk k sk)

    have over₁ : ∀ R : SchemeHomOver (geomPoint k sk) E₁.f, (R.1 ≫ g₁) ≫ E.f = geomPoint k (sk.comp ρ) := by
      intro R
      rw [Category.assoc, sq₁.w, ← Category.assoc, R.2, hgeom]
    let Ψ₁ : C₁ → CE := fun R => ⟨⟨R.1.1 ≫ g₁, over₁ R.1⟩, hlev₁ _ R.1 R.2⟩
    have Ψ₁inj : Function.Injective Ψ₁ := by
      intro R R' hRR'
      have h1 : R.1.1 ≫ g₁ = R'.1.1 ≫ g₁ := congrArg (fun z : CE => z.1.1) hRR'
      apply Subtype.ext; apply Subtype.ext
      exact sq₁.hom_ext h1 (by rw [R.1.2, R'.1.2])

    have Ψ₁surj : Function.Surjective Ψ₁ := by
      let F : ZMod N × ZMod N → ZMod N × ZMod N := fun z => eE.symm (Ψ₁ (e₁ z))
      have hF : Function.Injective F := by
        intro z z' hz
        exact e₁.injective (Ψ₁inj (eE.symm.injective hz))
      have hFb : Function.Bijective F := Finite.injective_iff_bijective.mp hF
      intro y
      obtain ⟨z, hz⟩ := hFb.2 (eE.symm y)
      exact ⟨e₁ z, eE.symm.injective hz⟩

    have overQ : (Q.1 ≫ g₂) ≫ E.f = geomPoint k (sk.comp ρ) := by
      rw [Category.assoc, sq₂.w, ← Category.assoc, Q.2, hgeom]
    obtain ⟨R, hR⟩ := Ψ₁surj ⟨⟨Q.1 ≫ g₂, overQ⟩, hlev₂ _ Q hQ⟩
    have hR1 : R.1.1 ≫ g₁ = Q.1 ≫ g₂ := congrArg (fun z : CE => z.1.1) hR
    have hRΦ : R.1 = Φ (geomPoint k sk) Q := by
      apply Subtype.ext
      show R.1.1 = Q.1 ≫ h
      apply sq₁.hom_ext
      · rw [hR1, Category.assoc, hg]
      · rw [R.1.2, Category.assoc, hf, Q.2]
    rw [← hRΦ]
    exact R.2

  refine ⟨h, hg, hf, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by rw [hid]; infer_instance
    exact IsPullback.of_horiz_isIso ⟨by rw [hid, Category.comp_id, hf]⟩
  ·
    intro T t' P Q
    rw [Φmul t' P Q]
    symm
    apply reindex E₁.L t' _ (by rw [hid, Category.comp_id])
    · rfl
    · rfl
  ·
    intro x
    apply sq₁.hom_ext
    · rw [Category.assoc, hg, Category.assoc, hact₁, ← Category.assoc, hg, hact₂]
    · rw [Category.assoc, hf, E₂.act_over, Category.assoc, E₁.act_over, hf]
  ·
    intro T t' P hP
    show FactorsThrough E₁.lev (Φ t' P)
    refine (crit₁ t' _).2 ⟨?_, ?_⟩
    · rw [← Φ_nsmul, E₂.lev_torsion t' P hP, Φ_one]
    · intro k _ _ sk τ hτ
      have hcomm : schemeHomOverComp τ hτ (Φ t' P) = Φ (geomPoint k sk) (schemeHomOverComp τ hτ P) :=
        Subtype.ext (by simp only [schemeHomOverComp_coe, Φ, Category.assoc])
      rw [hcomm]
      apply geomlev
      obtain ⟨P₀, hP₀⟩ := hP
      exact ⟨τ ≫ P₀, by rw [Category.assoc, hP₀]; rfl⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_comp_eq_of_isPullbackVia_of_isPullbackVia_of_isUnit (solution)
