-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_lev_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0a6baee5-31ac-5a9c-a8ca-ea4f7d6869ee

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_lev_lift
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal"

open scoped Quaternion TensorProduct NumberField

universe u

namespace T4Aux

section GroupLaw
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem nsmulPt_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n P) = nsmulPt L t' n (schemeHomOverComp ψ hψ P) := by
  rw [nsmulPt_eq_nsmul, nsmulPt_eq_nsmul]; exact L.nsmul_natural t t' ψ hψ n P

theorem one_coe_eq (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← this]; rfl

theorem coe_comp_schemeNsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : P.1 ≫ L.schemeNsmul n = (nsmulPt L t n P).1 := by
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := by
    apply Subtype.ext; simp [RelativeGroupLaw.idPoint]
  have := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  rw [hP] at this
  rw [nsmulPt_eq_nsmul, ← this]; rfl

theorem exists_comp_fst_eq_iff_nsmulPt_eq_one (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    (∃ κ : T ⟶ L.schemeKer n,
        κ ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = P.1) ↔
      nsmulPt L t n P = L.one t := by
  have he : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  constructor
  · rintro ⟨κ, hκ⟩
    apply Subtype.ext
    have hsnd : κ ≫ pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = t := by
      have h1 : pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f =
          pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
        calc pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f
            = pullback.fst _ _ ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]
          _ = (pullback.fst _ _ ≫ L.schemeNsmul n) ≫ f := (Category.assoc _ _ _).symm
          _ = (pullback.snd _ _ ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by rw [pullback.condition]
          _ = pullback.snd _ _ := by rw [Category.assoc, he, Category.comp_id]
      rw [← P.2, ← hκ, Category.assoc, h1]
    rw [← coe_comp_schemeNsmul, one_coe_eq, ← hκ, Category.assoc, pullback.condition, ← Category.assoc, hsnd]
  · intro h
    refine ⟨pullback.lift P.1 t ?_, pullback.lift_fst _ _ _⟩
    rw [coe_comp_schemeNsmul, h, one_coe_eq]

theorem nsmulPt_eq_one_comp (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f)
    (h : nsmulPt L t n P = L.one t) : nsmulPt L t' n (schemeHomOverComp ψ hψ P) = L.one t' := by
  rw [← nsmulPt_natural, h]; exact L.one_natural t t' ψ hψ

theorem nsmulPt_eq_pow (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t; nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem nsmulPt_one' (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    nsmulPt L t n (L.one t) = L.one t := by
  letI := L.pointGroup t
  have := nsmulPt_eq_pow L t n (L.one t)
  rw [this]; exact one_pow n

theorem nsmulPt_mul (L : RelativeGroupLaw R f) (hc : L.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P Q : SchemeHomOver t f) :
    nsmulPt L t n (L.mul t P Q) = L.mul t (nsmulPt L t n P) (nsmulPt L t n Q) := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := hc t }
  have h1 := nsmulPt_eq_pow L t n (L.mul t P Q)
  have h2 := nsmulPt_eq_pow L t n P
  have h3 := nsmulPt_eq_pow L t n Q
  rw [h1, h2, h3]; exact mul_pow P Q n

theorem nsmulPt_inv (L : RelativeGroupLaw R f) (hc : L.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n (L.inv t P) = L.inv t (nsmulPt L t n P) := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := hc t }
  have h1 := nsmulPt_eq_pow L t n (L.inv t P)
  have h2 := nsmulPt_eq_pow L t n P
  rw [h1, h2]; exact inv_pow P n

theorem pushPt_nsmulPt (L : RelativeGroupLaw R f) (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    pushPt φ hφ (nsmulPt L t n P) = nsmulPt L t n (pushPt φ hφ P) := by
  have hone : pushPt φ hφ (L.one t) = L.one t := by
    letI := L.pointGroup t
    have h := hhom t (L.one t) (L.one t)
    rw [L.one_mul] at h
    have : pushPt φ hφ (L.one t) * pushPt φ hφ (L.one t) = pushPt φ hφ (L.one t) * 1 := by
      rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  induction n with
  | zero => exact hone
  | succ n ih => show pushPt φ hφ (L.mul t _ _) = L.mul t _ _; rw [hhom, ih]

def castPt {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (P : SchemeHomOver t f) :
    SchemeHomOver t' f := ⟨P.1, by rw [← h]; exact P.2⟩

@[scoped simp] theorem castPt_coe {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (P : SchemeHomOver t f) : (castPt h P).1 = P.1 := rfl

theorem castPt_mul (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)}
    (h : t = t') (P Q : SchemeHomOver t f) :
    castPt h (L.mul t P Q) = L.mul t' (castPt h P) (castPt h Q) := by
  subst h; rfl

theorem castPt_injective {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') :
    Function.Injective (castPt (f := f) h) := by
  intro P Q hPQ; apply Subtype.ext
  have := congrArg Subtype.val hPQ
  simpa only [castPt_coe] using this

theorem mapPt_nsmulPt {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  have hone : mapPt φ hφ (L.one t) = L'.one t := by
    letI := L'.pointGroup t
    have h := hhom t (L.one t) (L.one t)
    rw [L.one_mul] at h
    have : mapPt φ hφ (L.one t) * mapPt φ hφ (L.one t) = mapPt φ hφ (L.one t) * 1 := by
      rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  induction n with
  | zero => exact hone
  | succ n ih => show mapPt φ hφ (L.mul t _ _) = L'.mul t _ _; rw [hhom, ih]

end GroupLaw

section Hom

variable {B B₀ : Type u} [CommRing B] [CommRing B₀] (φ : B →+* B₀)
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
  {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)} (L₀ : RelativeGroupLaw B₀ f₀)
  (g : A₀ ⟶ A) (hgw : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom φ))

def gPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of B₀)} (P : SchemeHomOver t f₀) :
    SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hgw, ← Category.assoc, P.2]⟩

@[scoped simp] theorem gPt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of B₀)} (P : SchemeHomOver t f₀) :
    (gPt φ g hgw P).1 = P.1 ≫ g := rfl

variable (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
    gPt φ g hgw (L₀.mul t P Q) = L.mul _ (gPt φ g hgw P) (gPt φ g hgw Q))

include hmul in
theorem gPt_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B₀)) :
    gPt φ g hgw (L₀.one t) = L.one _ := by
  letI := L.pointGroup (t ≫ Spec.map (CommRingCat.ofHom φ))
  have h := hmul t (L₀.one t) (L₀.one t)
  rw [L₀.one_mul] at h

  have : gPt φ g hgw (L₀.one t) * gPt φ g hgw (L₀.one t) = gPt φ g hgw (L₀.one t) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel this

include hmul in
theorem gPt_nsmulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B₀)) (n : ℕ) (P : SchemeHomOver t f₀) :
    gPt φ g hgw (nsmulPt L₀ t n P) = nsmulPt L _ n (gPt φ g hgw P) := by
  induction n with
  | zero => exact gPt_one φ L L₀ g hgw hmul t
  | succ n ih => show gPt φ g hgw (L₀.mul t _ _) = L.mul _ _ _; rw [hmul, ih]

include hmul in
theorem gPt_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t f₀) :
    gPt φ g hgw (L₀.inv t P) = L.inv _ (gPt φ g hgw P) := by
  letI := L.pointGroup (t ≫ Spec.map (CommRingCat.ofHom φ))
  have h := hmul t (L₀.inv t P) P
  rw [L₀.inv_mul_cancel, gPt_one φ L L₀ g hgw hmul] at h

  exact (eq_inv_of_mul_eq_one_left h.symm)

end Hom

end T4Aux
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_lev_lift.T4Aux"

open T4Aux in

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hN : IsUnit ((N : ℕ) : B))
    (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀)
    (g : E₀.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (hg_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t E₀.f),
      (E₀.L.mul t P Q).1 ≫ g =
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x) :
    ∃ E' : FakeEllipticCurve Λ N B, ∃ (e : E'.A ≅ E.A) (he : e.hom ≫ E.f = E'.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E'.f),
        mapPt e.hom he (E'.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
      (∀ x : ↥Λ, E'.act x ≫ e.hom = e.hom ≫ E.act x) ∧

      FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E' E₀ (g ≫ e.inv) ∧

      (∀ (E'' : FakeEllipticCurve Λ N B) (e'' : E''.A ≅ E.A) (he'' : e''.hom ≫ E.f = E''.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E''.f),
          mapPt e''.hom he'' (E''.L.mul t P Q) = E.L.mul t (mapPt e''.hom he'' P) (mapPt e''.hom he'' Q)) →
        (∀ x : ↥Λ, E''.act x ≫ e''.hom = e''.hom ≫ E.act x) →
        FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E'' E₀ (g ≫ e''.inv) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t E.f),
          FactorsThrough E'.lev (mapPt e.inv (by rw [Iso.inv_comp_eq, he]) P) ↔
            FactorsThrough E''.lev (mapPt e''.inv (by rw [Iso.inv_comp_eq, he'']) P)) := by
  classical

  have hN₀ : IsUnit ((N : ℕ) : B₀) := by simpa using hN.map (algebraMap B B₀)
  obtain ⟨hKfin, hKet⟩ := E.isFinite_and_etale_schemeKerStr_of_isUnit N hN
  obtain ⟨hK₀fin, hK₀et⟩ := E₀.isFinite_and_etale_schemeKerStr_of_isUnit N hN₀
  set eB := (E.L.one (𝟙 (Spec (CommRingCat.of B)))).1 with heB
  set eB₀ := (E₀.L.one (𝟙 (Spec (CommRingCat.of B₀)))).1 with heB₀
  set ιK := pullback.fst (E.L.schemeNsmul N) eB with hιK
  set ιK₀ := pullback.fst (E₀.L.schemeNsmul N) eB₀ with hιK₀

  obtain ⟨hgci, hgsurj, hghom⟩ :=
    AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker (algebraMap B B₀) hπ hker
      E.f E₀.f g hg

  haveI := E₀.lev_closed; haveI := E₀.lev_flat; haveI := E₀.lev_finitePresentation; haveI := hK₀et
  obtain ⟨U₀, e₀, hU₀cl, he₀, hU₀pts⟩ :=
    E₀.L.exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one N E₀.lev
      (fun t P h => E₀.lev_torsion t P h)

  have hgw : g ≫ E.f = E₀.f ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) := hg.w
  have hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t E₀.f),
      gPt (algebraMap B B₀) g hgw (E₀.L.mul t P Q) =
        E.L.mul _ (gPt (algebraMap B B₀) g hgw P) (gPt (algebraMap B B₀) g hgw Q) :=
    fun t P Q => Subtype.ext (hg_mul t P Q)
  have hact : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
      gPt (algebraMap B B₀) g hgw (pushPt (E₀.act x) (E₀.act_over x) P) =
        pushPt (E.act x) (E.act_over x) (gPt (algebraMap B B₀) g hgw P) := by
    intro x T t P; apply Subtype.ext; simp [gPt, mapPt, hg_act x]

  have hlift : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀))
      (Q : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) E.f),
      ∃ P : SchemeHomOver t E₀.f, gPt (algebraMap B B₀) g hgw P = Q := by
    intro T t Q
    refine ⟨⟨hg.lift Q.1 t Q.2, hg.lift_snd _ _ _⟩, Subtype.ext (hg.lift_fst _ _ _)⟩

  have hginj : Function.Injective g.base := hghom.injective

  have hgN : g ≫ E.L.schemeNsmul N = E₀.L.schemeNsmul N ≫ g := by
    have h1 := coe_comp_schemeNsmul E.L _ N (gPt (algebraMap B B₀) g hgw (RelativeGroupLaw.idPoint (f := E₀.f)))
    have h2 := gPt_nsmulPt (algebraMap B B₀) E.L E₀.L g hgw hmul E₀.f N (RelativeGroupLaw.idPoint (f := E₀.f))
    rw [← h2] at h1
    simpa [gPt, RelativeGroupLaw.idPoint, RelativeGroupLaw.schemeNsmul, nsmulPt_eq_nsmul] using h1
  have hge : eB₀ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap B B₀)) ≫ eB := by
    have h1 := gPt_one (algebraMap B B₀) E.L E₀.L g hgw hmul (𝟙 _)
    have h2 := congrArg Subtype.val h1
    rw [one_coe_eq E.L] at h2
    simpa [gPt] using h2

  set V : Set ↥E.A := g.base '' (ιK₀.base '' (U₀ : Set ↥(E₀.L.schemeKer N))) with hV

  let Good : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)}, SchemeHomOver t E.f → Prop :=
    fun {T} {t} Q => nsmulPt E.L t N Q = E.L.one t ∧ Set.range Q.1.base ⊆ V

  have hφsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap B B₀))) := by
    have sq : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B B₀))) (𝟙 _) (𝟙 _)
        (Spec.map (CommRingCat.ofHom (algebraMap B B₀))) :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    exact (AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker (algebraMap B B₀)
      hπ hker (𝟙 _) (𝟙 _) _ sq).2.1

  haveI : IsSeparated E.f := E.bundle.proper.toIsSeparated
  haveI : IsSeparated E₀.f := E₀.bundle.proper.toIsSeparated
  haveI heBci : IsClosedImmersion eB := by
    have : IsClosedImmersion (eB ≫ E.f) := by rw [(E.L.one (𝟙 _)).2]; infer_instance
    exact IsClosedImmersion.of_comp eB E.f
  haveI heB₀ci : IsClosedImmersion eB₀ := by
    have : IsClosedImmersion (eB₀ ≫ E₀.f) := by rw [(E₀.L.one (𝟙 _)).2]; infer_instance
    exact IsClosedImmersion.of_comp eB₀ E₀.f
  haveI hιKci : IsClosedImmersion ιK := inferInstance
  haveI hιK₀ci : IsClosedImmersion ιK₀ := inferInstance

  have hKrange : Set.range ιK.base ⊆ g.base '' Set.range ιK₀.base := by
    intro y hy
    rw [hιK, Scheme.Pullback.range_fst] at hy
    obtain ⟨x₀, rfl⟩ := hgsurj.1 y
    refine ⟨x₀, ?_, rfl⟩
    rw [hιK₀, Scheme.Pullback.range_fst]

    obtain ⟨s, hs⟩ := hy
    obtain ⟨s₀, rfl⟩ := hφsurj.1 s
    refine ⟨s₀, hginj ?_⟩
    have h1 : g.base (eB₀.base s₀) = eB.base ((Spec.map (CommRingCat.ofHom (algebraMap B B₀))).base s₀) := by
      have := congrArg (fun h => h.base s₀) hge; simpa using this
    have h2 : g.base ((E₀.L.schemeNsmul N).base x₀) = (E.L.schemeNsmul N).base (g.base x₀) := by
      have := congrArg (fun h => h.base x₀) hgN; simpa using this.symm
    rw [h1, h2]; exact hs

  have hVcl : IsClosed V := by
    rw [hV]
    exact g.isClosedEmbedding.isClosedMap _ (ιK₀.isClosedEmbedding.isClosedMap _ hU₀cl)
  obtain ⟨O₀, hO₀open, hO₀⟩ : ∃ O₀ : Set ↥E₀.A, IsOpen O₀ ∧ ιK₀.base ⁻¹' O₀ = (U₀ : Set _) :=
    ιK₀.isClosedEmbedding.isInducing.isOpen_iff.1 U₀.2
  have hUeq : ιK.base ⁻¹' V = ιK.base ⁻¹' (g.base '' O₀) := by
    ext κ
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
      refine ⟨ιK₀.base z, ?_, hy⟩
      have : z ∈ ιK₀.base ⁻¹' O₀ := by rw [hO₀]; exact hz
      exact this
    · rintro ⟨y, hy, hyκ⟩
      obtain ⟨y', ⟨z, rfl⟩, hy'⟩ := hKrange ⟨κ, rfl⟩
      have : y = ιK₀.base z := hginj (hyκ.trans hy'.symm)
      subst this
      refine ⟨ιK₀.base z, ⟨z, ?_, rfl⟩, hyκ⟩
      show z ∈ (U₀ : Set _)
      rw [← hO₀]; exact hy
  have hUopen : IsOpen (ιK.base ⁻¹' V) := by
    rw [hUeq]; exact (hghom.isOpenMap _ hO₀open).preimage ιK.base.hom.continuous
  have hUcl : IsClosed (ιK.base ⁻¹' V) := hVcl.preimage ιK.base.hom.continuous
  let U : (E.L.schemeKer N).Opens := ⟨ιK.base ⁻¹' V, hUopen⟩
  have hUV : ∀ κ, κ ∈ (U : Set _) ↔ ιK.base κ ∈ V := fun κ => Iff.rfl
  have hιK₀inj : Function.Injective ιK₀.base := ιK₀.isClosedEmbedding.injective

  have F1 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (Q : SchemeHomOver t E.f),
      FactorsThrough (U.ι ≫ ιK) Q ↔ Good Q := by
    intro T t Q
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨(exists_comp_fst_eq_iff_nsmulPt_eq_one E.L t N Q).1 ⟨c ≫ U.ι, by rw [Category.assoc]; exact hc⟩, ?_⟩
      rintro _ ⟨x, rfl⟩
      have h1 : Q.1.base x = ιK.base (U.ι.base (c.base x)) := by
        rw [← hc]; rfl
      rw [h1]
      exact (hUV _).1 (by rw [← Scheme.Opens.range_ι]; exact ⟨c.base x, rfl⟩)
    · rintro ⟨htor, hVQ⟩
      obtain ⟨κ, hκ⟩ := (exists_comp_fst_eq_iff_nsmulPt_eq_one E.L t N Q).2 htor
      have hκU : Set.range κ.base ⊆ Set.range U.ι.base := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨x, rfl⟩
        show ιK.base (κ.base x) ∈ V
        apply hVQ
        refine ⟨x, ?_⟩
        rw [← hκ]; rfl
      refine ⟨IsOpenImmersion.lift U.ι κ hκU, ?_⟩
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hκ]

  have F2 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
      FactorsThrough E₀.lev P ↔ Good (gPt (algebraMap B B₀) g hgw P) := by
    intro T t P
    rw [hU₀pts t P]
    constructor
    · rintro ⟨κ₀, hκ₀, hr⟩
      refine ⟨?_, ?_⟩
      · have h0 := (exists_comp_fst_eq_iff_nsmulPt_eq_one E₀.L t N P).1 ⟨κ₀, hκ₀⟩
        rw [← gPt_nsmulPt (algebraMap B B₀) E.L E₀.L g hgw hmul, h0,
          gPt_one (algebraMap B B₀) E.L E₀.L g hgw hmul]
      · rintro _ ⟨x, rfl⟩
        refine ⟨ιK₀.base (κ₀.base x), ⟨κ₀.base x, hr ⟨x, rfl⟩, rfl⟩, ?_⟩
        show g.base (ιK₀.base (κ₀.base x)) = (P.1 ≫ g).base x
        rw [← hκ₀]; rfl
    · rintro ⟨htor, hVP⟩
      have h0 : nsmulPt E₀.L t N P = E₀.L.one t := by
        have h1 : gPt (algebraMap B B₀) g hgw (nsmulPt E₀.L t N P) =
            gPt (algebraMap B B₀) g hgw (E₀.L.one t) := by
          rw [gPt_nsmulPt (algebraMap B B₀) E.L E₀.L g hgw hmul, htor,
            gPt_one (algebraMap B B₀) E.L E₀.L g hgw hmul]
        have h2 := congrArg Subtype.val h1
        simp only [gPt_coe] at h2
        exact Subtype.ext (hg.hom_ext h2 (by rw [(nsmulPt E₀.L t N P).2, (E₀.L.one t).2]))
      obtain ⟨κ₀, hκ₀⟩ := (exists_comp_fst_eq_iff_nsmulPt_eq_one E₀.L t N P).2 h0
      refine ⟨κ₀, hκ₀, ?_⟩
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hVP ⟨x, rfl⟩
      have h3 : (gPt (algebraMap B B₀) g hgw P).1.base x = g.base (ιK₀.base (κ₀.base x)) := by
        show (P.1 ≫ g).base x = _; rw [← hκ₀]; rfl
      rw [h3] at hy
      have : z = κ₀.base x := hιK₀inj (hginj hy)
      rw [← this]; exact hz

  have F3 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (Q : SchemeHomOver t E.f),
      Set.range (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap B B₀))) ≫ Q.1).base ⊆ V →
        Set.range Q.1.base ⊆ V := by
    intro T t Q h
    have hsurj : Function.Surjective (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap B B₀)))).base :=
      (AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker (algebraMap B B₀) hπ hker
        t (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) _ (IsPullback.of_hasPullback _ _)).2.1.1
    rintro _ ⟨x, rfl⟩
    obtain ⟨x₀, rfl⟩ := hsurj x
    apply h
    exact ⟨x₀, by simp⟩

  set sφ := Spec.map (CommRingCat.ofHom (algebraMap B B₀)) with hsφ
  have resGood : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (Q : SchemeHomOver t E.f), Good Q →
      Good (schemeHomOverComp (pullback.fst t sφ) pullback.condition Q) := by
    intro T t Q hQ
    refine ⟨nsmulPt_eq_one_comp E.L t _ _ _ N Q hQ.1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hQ.2 ⟨(pullback.fst t sφ).base x, rfl⟩

  have resLift : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (Q : SchemeHomOver t E.f), Good Q →
      ∃ P : SchemeHomOver (pullback.snd t sφ) E₀.f,
        gPt (algebraMap B B₀) g hgw P = schemeHomOverComp (pullback.fst t sφ) pullback.condition Q ∧
        FactorsThrough E₀.lev P := by
    intro T t Q hQ
    obtain ⟨P, hP⟩ := hlift (pullback.snd t sφ) (schemeHomOverComp (pullback.fst t sφ) pullback.condition Q)
    refine ⟨P, hP, (F2 _ P).2 ?_⟩
    rw [hP]; exact resGood t Q hQ

  have goodOfRes : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (Q : SchemeHomOver t E.f)
      (P : SchemeHomOver (pullback.snd t sφ) E₀.f),
      gPt (algebraMap B B₀) g hgw P = schemeHomOverComp (pullback.fst t sφ) pullback.condition Q →
      FactorsThrough E₀.lev P → nsmulPt E.L t N Q = E.L.one t → Good Q := by
    intro T t Q P hP hlevP htor
    refine ⟨htor, F3 t Q ?_⟩
    have hG := (F2 _ P).1 hlevP
    rw [hP] at hG
    exact hG.2

  have good_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)), Good (E.L.one t) := by
    intro T t
    refine goodOfRes t (E.L.one t) (E₀.L.one _) ?_ (E₀.lev_one _) (nsmulPt_one' E.L t N)
    rw [gPt_one (algebraMap B B₀) E.L E₀.L g hgw hmul]
    exact (E.L.one_natural t _ (pullback.fst t sφ) pullback.condition).symm
  have good_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t E.f),
      Good P → Good Q → Good (E.L.mul t P Q) := by
    intro T t P Q hP hQ
    obtain ⟨P₁, hP₁, hlP₁⟩ := resLift t P hP
    obtain ⟨Q₁, hQ₁, hlQ₁⟩ := resLift t Q hQ
    refine goodOfRes t _ (E₀.L.mul _ P₁ Q₁) ?_ ((E₀.lev_sub _ P₁ Q₁ hlP₁ hlQ₁).1) ?_
    · rw [hmul, hP₁, hQ₁]; exact (E.L.mul_natural t _ (pullback.fst t sφ) pullback.condition P Q).symm
    · rw [nsmulPt_mul E.L E.comm, hP.1, hQ.1, E.L.one_mul]
  have good_inv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t E.f),
      Good P → Good (E.L.inv t P) := by
    intro T t P hP
    obtain ⟨P₁, hP₁, hlP₁⟩ := resLift t P hP
    refine goodOfRes t _ (E₀.L.inv _ P₁) ?_ ((E₀.lev_sub _ P₁ P₁ hlP₁ hlP₁).2) ?_
    · rw [gPt_inv (algebraMap B B₀) E.L E₀.L g hgw hmul, hP₁]

      letI := E.L.pointGroup (pullback.snd t sφ ≫ sφ)
      symm
      apply eq_inv_of_mul_eq_one_left
      show E.L.mul _ (schemeHomOverComp _ _ (E.L.inv t P)) (schemeHomOverComp _ _ P) = E.L.one _
      rw [← E.L.mul_natural, E.L.inv_mul_cancel]; exact E.L.one_natural t _ _ _
    · letI := E.L.pointGroup t
      rw [nsmulPt_inv E.L E.comm, hP.1]; exact inv_one
  have good_act : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t E.f),
      Good P → Good (pushPt (E.act x) (E.act_over x) P) := by
    intro x T t P hP
    obtain ⟨P₁, hP₁, hlP₁⟩ := resLift t P hP
    refine goodOfRes t _ (pushPt (E₀.act x) (E₀.act_over x) P₁) ?_ (E₀.lev_stable x _ P₁ hlP₁) ?_
    · rw [hact, hP₁]; apply Subtype.ext; simp [pushPt, mapPt, schemeHomOverComp]
    · rw [← pushPt_nsmulPt E.L (E.act x) (E.act_over x) (E.act_hom x), hP.1]
      exact pushPt_nsmulPt E.L (E.act x) (E.act_over x) (E.act_hom x) t 0 P

  have hιKf : ιK ≫ E.f = E.L.schemeKerStr N := by
    calc ιK ≫ E.f = ιK ≫ (E.L.schemeNsmul N ≫ E.f) := by rw [E.L.schemeNsmul_over]
      _ = (ιK ≫ E.L.schemeNsmul N) ≫ E.f := (Category.assoc _ _ _).symm
      _ = (pullback.snd _ _ ≫ eB) ≫ E.f := by rw [hιK, pullback.condition]
      _ = E.L.schemeKerStr N := by rw [Category.assoc, (E.L.one (𝟙 _)).2, Category.comp_id]
  haveI hUιci : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hUcl)
  haveI : IsFinite (E.L.schemeKerStr N) := hKfin
  haveI : Etale (E.L.schemeKerStr N) := hKet
  have hlev_finite : IsFinite ((U.ι ≫ ιK) ≫ E.f) := by rw [Category.assoc, hιKf]; infer_instance
  have hlev_flat : Flat ((U.ι ≫ ιK) ≫ E.f) := by rw [Category.assoc, hιKf]; infer_instance
  have hlev_lfp : LocallyOfFinitePresentation ((U.ι ≫ ιK) ≫ E.f) := by rw [Category.assoc, hιKf]; infer_instance

  have hιK₀f' : ιK₀ ≫ E₀.f = E₀.L.schemeKerStr N := by
    calc ιK₀ ≫ E₀.f = ιK₀ ≫ (E₀.L.schemeNsmul N ≫ E₀.f) := by rw [E₀.L.schemeNsmul_over]
      _ = (ιK₀ ≫ E₀.L.schemeNsmul N) ≫ E₀.f := (Category.assoc _ _ _).symm
      _ = (pullback.snd _ _ ≫ eB₀) ≫ E₀.f := by rw [hιK₀, pullback.condition]
      _ = E₀.L.schemeKerStr N := by rw [Category.assoc, (E₀.L.one (𝟙 _)).2, Category.comp_id]
  have hkw : (ιK₀ ≫ g) ≫ E.L.schemeNsmul N = (E₀.L.schemeKerStr N ≫ sφ) ≫ eB := by
    rw [Category.assoc, hgN, ← Category.assoc, hιK₀, pullback.condition, Category.assoc, hge,
      Category.assoc]
  let kK : E₀.L.schemeKer N ⟶ E.L.schemeKer N := pullback.lift (ιK₀ ≫ g) (E₀.L.schemeKerStr N ≫ sφ) hkw
  have hkK₁ : kK ≫ ιK = ιK₀ ≫ g := pullback.lift_fst _ _ _
  have hkK₂ : kK ≫ E.L.schemeKerStr N = E₀.L.schemeKerStr N ≫ sφ := pullback.lift_snd _ _ _
  have hkpb : IsPullback kK (E₀.L.schemeKerStr N) (E.L.schemeKerStr N) sφ := by
    refine IsPullback.of_isLimit' ⟨hkK₂⟩ (PullbackCone.IsLimit.mk hkK₂ ?_ ?_ ?_ ?_)
    · intro s
      have hs : (s.fst ≫ ιK) ≫ E.f = s.snd ≫ sφ := by rw [Category.assoc, hιKf]; exact s.condition
      refine pullback.lift (hg.lift (s.fst ≫ ιK) s.snd hs) s.snd ?_
      apply hg.hom_ext
      · calc (hg.lift (s.fst ≫ ιK) s.snd hs ≫ E₀.L.schemeNsmul N) ≫ g
            = hg.lift (s.fst ≫ ιK) s.snd hs ≫ (E₀.L.schemeNsmul N ≫ g) := Category.assoc _ _ _
          _ = hg.lift (s.fst ≫ ιK) s.snd hs ≫ (g ≫ E.L.schemeNsmul N) := by rw [hgN]
          _ = (hg.lift (s.fst ≫ ιK) s.snd hs ≫ g) ≫ E.L.schemeNsmul N := (Category.assoc _ _ _).symm
          _ = (s.fst ≫ ιK) ≫ E.L.schemeNsmul N := by rw [hg.lift_fst]
          _ = s.fst ≫ (ιK ≫ E.L.schemeNsmul N) := Category.assoc _ _ _
          _ = s.fst ≫ (pullback.snd (E.L.schemeNsmul N) eB ≫ eB) := by rw [hιK, pullback.condition]
          _ = (s.fst ≫ E.L.schemeKerStr N) ≫ eB := (Category.assoc _ _ _).symm
          _ = (s.snd ≫ sφ) ≫ eB := by rw [s.condition]
          _ = s.snd ≫ (sφ ≫ eB) := Category.assoc _ _ _
          _ = s.snd ≫ (eB₀ ≫ g) := by rw [hge]
          _ = (s.snd ≫ eB₀) ≫ g := (Category.assoc _ _ _).symm
      · rw [Category.assoc, E₀.L.schemeNsmul_over, hg.lift_snd, Category.assoc, (E₀.L.one (𝟙 _)).2,
          Category.comp_id]
    · intro s
      apply pullback.hom_ext
      · rw [Category.assoc, hkK₁, ← Category.assoc, pullback.lift_fst, hg.lift_fst]
      · rw [Category.assoc, hkK₂, ← Category.assoc, pullback.lift_snd, s.condition]
    · intro s; exact pullback.lift_snd _ _ _
    · intro s m hm₁ hm₂
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        apply hg.hom_ext
        · rw [Category.assoc, ← hkK₁, ← Category.assoc, hm₁, hg.lift_fst]
        · rw [Category.assoc, hιK₀f', hm₂, hg.lift_snd]
      · rw [pullback.lift_snd, hm₂]
  have hkU : kK ⁻¹ᵁ U = U₀ := by
    ext z
    show ιK.base ((kK).base z) ∈ V ↔ z ∈ (U₀ : Set _)
    have h1 : ιK.base (kK.base z) = g.base (ιK₀.base z) := by
      have := congrArg (fun h => h.base z) hkK₁; exact this
    rw [h1]
    constructor
    · rintro ⟨_, ⟨z', hz', rfl⟩, h⟩
      have : z' = z := hιK₀inj (hginj h)
      rw [← this]; exact hz'
    · intro hz; exact ⟨ιK₀.base z, ⟨z, hz, rfl⟩, rfl⟩
  have hUpb : IsPullback (kK ∣_ U) ((kK ⁻¹ᵁ U).ι ≫ E₀.L.schemeKerStr N) (U.ι ≫ E.L.schemeKerStr N) sφ :=
    (isPullback_morphismRestrict kK U).paste_vert hkpb
  have hlev_rank : ∀ s : ↥(Spec (CommRingCat.of B)), ((U.ι ≫ ιK) ≫ E.f).finrank s = N ^ 2 := by
    intro s
    obtain ⟨s₀, rfl⟩ := hφsurj.1 s
    haveI : Flat (U.ι ≫ E.L.schemeKerStr N) := inferInstance
    haveI : IsFinite (U.ι ≫ E.L.schemeKerStr N) := inferInstance
    rw [Category.assoc, hιKf, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hUpb s₀]

    have h1 : (kK ⁻¹ᵁ U).ι = ((E₀.L.schemeKer N).isoOfEq hkU).hom ≫ U₀.ι :=
      ((E₀.L.schemeKer N).isoOfEq_hom_ι hkU).symm
    haveI : IsFinite (E₀.L.schemeKerStr N) := hK₀fin
    haveI hU₀ιci : IsClosedImmersion U₀.ι :=
      IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU₀cl)
    haveI : Flat (U₀.ι ≫ E₀.L.schemeKerStr N) := inferInstance
    haveI : IsFinite (U₀.ι ≫ E₀.L.schemeKerStr N) := inferInstance
    rw [h1, Category.assoc, Scheme.Hom.finrank_comp_left_of_isIso]
    have h2 : E₀.lev ≫ E₀.f = e₀.hom ≫ (U₀.ι ≫ E₀.L.schemeKerStr N) := by
      rw [← he₀, Category.assoc, Category.assoc, hιK₀f']
    have h3 := E₀.lev_rank s₀
    rw [h2, Scheme.Hom.finrank_comp_left_of_isIso] at h3
    exact h3

  have hlev_fibre : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k), (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (U.ι ≫ ιK) P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) = E.L.mul (geomPoint k sk) (e x) (e y) := by
    intro k _ _ sk hNk

    have hle : RingHom.ker (algebraMap B B₀) ≤ RingHom.ker sk := by
      intro x hx
      obtain ⟨n, hn⟩ := hker
      have hxn : x ^ n ∈ (RingHom.ker (algebraMap B B₀)) ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at hxn
      have hx0 : x ^ n = 0 := by simpa using hxn
      have : IsNilpotent (sk x) := ⟨n, by rw [← map_pow, hx0, map_zero]⟩
      exact (RingHom.mem_ker).2 this.eq_zero
    let sk₀ : B₀ →+* k :=
      (Ideal.Quotient.lift _ sk hle).comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
    have hsk : sk₀.comp (algebraMap B B₀) = sk := by
      ext x
      have h1 : (RingHom.quotientKerEquivOfSurjective hπ).symm (algebraMap B B₀ x) = Ideal.Quotient.mk _ x := by
        rw [RingEquiv.symm_apply_eq, RingHom.quotientKerEquivOfSurjective_apply_mk]
      simp [sk₀, h1]
    have ht : geomPoint k sk = geomPoint k sk₀ ≫ sφ := by
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hsk]
    obtain ⟨e₀, he₀⟩ := E₀.lev_fibre k sk₀ hNk
    let Φ : {P : SchemeHomOver (geomPoint k sk₀) E₀.f // FactorsThrough E₀.lev P} →
        {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (U.ι ≫ ιK) P} :=
      fun P => ⟨castPt ht.symm (gPt (algebraMap B B₀) g hgw P.1),
        (F1 _ (gPt (algebraMap B B₀) g hgw P.1)).2 ((F2 _ P.1).1 P.2)⟩
    have hΦinj : Function.Injective Φ := by
      intro P Q hPQ
      have h1 : P.1.1 ≫ g = Q.1.1 ≫ g := congrArg (fun z => (z.1).1) hPQ
      apply Subtype.ext; apply Subtype.ext
      exact hg.hom_ext h1 (by rw [P.1.2, Q.1.2])
    have hΦsurj : Function.Surjective Φ := by
      intro Q
      obtain ⟨P, hP⟩ := hlift (geomPoint k sk₀) (castPt ht Q.1)
      have hgood : Good (gPt (algebraMap B B₀) g hgw P) := by
        rw [hP]; exact (F1 _ (castPt ht Q.1)).1 Q.2
      refine ⟨⟨P, (F2 _ P).2 hgood⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show (gPt (algebraMap B B₀) g hgw P).1 = Q.1.1
      rw [hP]; rfl
    refine ⟨e₀.trans (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩), ?_⟩
    intro x y
    show (Φ (e₀ (x + y))).1 = E.L.mul _ (Φ (e₀ x)).1 (Φ (e₀ y)).1
    have h2 : (e₀ (x + y)).1 = E₀.L.mul _ (e₀ x).1 (e₀ y).1 := he₀ x y
    show castPt ht.symm (gPt (algebraMap B B₀) g hgw (e₀ (x + y)).1) =
      E.L.mul _ (castPt ht.symm (gPt (algebraMap B B₀) g hgw (e₀ x).1))
        (castPt ht.symm (gPt (algebraMap B B₀) g hgw (e₀ y).1))
    rw [h2, hmul, castPt_mul]

  let E' : FakeEllipticCurve Λ N B :=
    { E with
      C := ↑U
      lev := U.ι ≫ ιK
      lev_closed := inferInstance
      lev_sub := fun t P Q hP hQ => by
        rw [F1] at hP hQ; rw [F1, F1]; exact ⟨good_mul t P Q hP hQ, good_inv t P hP⟩
      lev_one := fun t => (F1 t _).2 (good_one t)
      lev_torsion := fun t P h => ((F1 t P).1 h).1
      lev_stable := fun x T t P h => (F1 t _).2 (good_act x t P ((F1 t P).1 h))
      lev_finite := hlev_finite
      lev_flat := hlev_flat
      lev_finitePresentation := hlev_lfp
      lev_rank := hlev_rank
      lev_fibre := hlev_fibre }
  have he : (Iso.refl E.A).hom ≫ E.f = E'.f := Category.id_comp _
  refine ⟨E', Iso.refl E.A, he, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    have h1 : ∀ (R' : SchemeHomOver t E'.f), mapPt (Iso.refl E.A).hom he R' = R' := fun R' =>
      Subtype.ext (Category.comp_id _)
    rw [h1, h1, h1]
  · intro x; show E.act x ≫ 𝟙 E.A = 𝟙 E.A ≫ E.act x; simp
  ·
    show FakeEllipticCurve.IsPullbackVia (algebraMap B B₀) E' E₀ (g ≫ 𝟙 E.A)
    rw [Category.comp_id]
    refine ⟨hg, hg_mul, hg_act, ?_⟩
    intro T t' P hP
    exact (F1 _ (gPt (algebraMap B B₀) g hgw P)).2 ((F2 t' P).1 hP)
  ·
    intro E'' e'' he'' hmul'' hact'' hpb'' T t P
    obtain ⟨hg'', -, -, hlev''⟩ := hpb''

    haveI := E''.lev_closed
    haveI : IsClosedImmersion (E''.lev ≫ e''.hom) := inferInstance
    have hlevf'' : (E''.lev ≫ e''.hom) ≫ E.f = E''.lev ≫ E''.f := by rw [Category.assoc, he'']
    haveI : Flat ((E''.lev ≫ e''.hom) ≫ E.f) := by rw [hlevf'']; exact E''.lev_flat
    haveI : LocallyOfFinitePresentation ((E''.lev ≫ e''.hom) ≫ E.f) := by
      rw [hlevf'']; exact E''.lev_finitePresentation

    have hback : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (Q : SchemeHomOver t E.f),
        FactorsThrough (E''.lev ≫ e''.hom) Q ↔
          FactorsThrough E''.lev (mapPt e''.inv (by rw [Iso.inv_comp_eq, he'']) Q) := by
      intro T t Q
      constructor
      · rintro ⟨c, hc⟩; exact ⟨c, by simp only [mapPt_coe, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
      · rintro ⟨c, hc⟩; refine ⟨c, ?_⟩
        simp only [mapPt_coe] at hc
        rw [← Category.assoc, hc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have htor'' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (Q : SchemeHomOver t E.f),
        FactorsThrough (E''.lev ≫ e''.hom) Q → nsmulPt E.L t N Q = E.L.one t := by
      intro T t Q hQ
      set Q'' : SchemeHomOver t E''.f := mapPt e''.inv (by rw [Iso.inv_comp_eq, he'']) Q with hQ''
      have hQe : mapPt e''.hom he'' Q'' = Q := Subtype.ext (by simp [hQ'', mapPt])
      have h1 := E''.lev_torsion t Q'' ((hback t Q).1 hQ)
      rw [← hQe, ← mapPt_nsmulPt E''.L E.L e''.hom he'' hmul'', h1]
      exact mapPt_nsmulPt E''.L E.L e''.hom he'' hmul'' t 0 Q''
    obtain ⟨U'', eC'', hU''cl, heC'', hU''pts⟩ :=
      E.L.exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one N (E''.lev ≫ e''.hom) htor''

    have hιK₀f : ιK₀ ≫ E₀.f = E₀.L.schemeKerStr N := by
      calc ιK₀ ≫ E₀.f = ιK₀ ≫ (E₀.L.schemeNsmul N ≫ E₀.f) := by rw [E₀.L.schemeNsmul_over]
        _ = (ιK₀ ≫ E₀.L.schemeNsmul N) ≫ E₀.f := (Category.assoc _ _ _).symm
        _ = (pullback.snd _ _ ≫ eB₀) ≫ E₀.f := by rw [hιK₀, pullback.condition]
        _ = E₀.L.schemeKerStr N := by rw [Category.assoc, (E₀.L.one (𝟙 _)).2, Category.comp_id]
    have hιKinj : Function.Injective ιK.base := ιK.isClosedEmbedding.injective
    have hsub : (U : Set ↥(E.L.schemeKer N)) ⊆ (U'' : Set ↥(E.L.schemeKer N)) := by
      intro y hy
      obtain ⟨_, ⟨z, hz, rfl⟩, hyz⟩ := (hUV y).1 hy
      let P₀ : SchemeHomOver ((E₀.L.schemeKer N).fromSpecResidueField z ≫ E₀.L.schemeKerStr N) E₀.f :=
        ⟨(E₀.L.schemeKer N).fromSpecResidueField z ≫ ιK₀, by rw [Category.assoc, hιK₀f]⟩
      have hP₀ : FactorsThrough E₀.lev P₀ := by
        rw [hU₀pts]
        refine ⟨(E₀.L.schemeKer N).fromSpecResidueField z, rfl, ?_⟩
        rintro _ ⟨x, rfl⟩
        rw [Scheme.fromSpecResidueField_apply]; exact hz
      obtain ⟨c, hc⟩ := hlev'' _ P₀ hP₀
      have hft : FactorsThrough (E''.lev ≫ e''.hom) (gPt (algebraMap B B₀) g hgw P₀) :=
        ⟨c, by rw [← Category.assoc, hc]; simp [gPt]⟩
      obtain ⟨κ, hκ, hr⟩ := (hU''pts _ _).1 hft

      let pt : ↥(Spec (CommRingCat.of ((E₀.L.schemeKer N).residueField z))) := Classical.arbitrary _
      have hκ' := congrArg (fun h => h.base pt) hκ
      have h2 : ((E₀.L.schemeKer N).fromSpecResidueField z ≫ ιK₀ ≫ g).base pt = g.base (ιK₀.base z) := by
        show g.base (ιK₀.base (((E₀.L.schemeKer N).fromSpecResidueField z).base pt)) = _
        rw [Scheme.fromSpecResidueField_apply]
      have h1 : ιK.base (κ.base pt) = ιK.base y := by
        rw [← hyz]; exact hκ'.trans h2
      rw [← hιKinj h1]
      exact hr ⟨pt, rfl⟩
    have himp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (Q : SchemeHomOver t E.f),
        FactorsThrough (U.ι ≫ ιK) Q → FactorsThrough (E''.lev ≫ e''.hom) Q := by
      intro T t Q hQ
      obtain ⟨htorQ, hVQ⟩ := (F1 t Q).1 hQ
      obtain ⟨κ, hκ⟩ := (exists_comp_fst_eq_iff_nsmulPt_eq_one E.L t N Q).2 htorQ
      refine (hU''pts t Q).2 ⟨κ, hκ, ?_⟩
      rintro _ ⟨x, rfl⟩
      apply hsub
      show ιK.base (κ.base x) ∈ V
      apply hVQ; exact ⟨x, by rw [← hκ]; rfl⟩

    have hsup : (U'' : Set ↥(E.L.schemeKer N)) ⊆ (U : Set ↥(E.L.schemeKer N)) := by
      intro y hy
      let K := E.L.schemeKer N
      let k : Type := AlgebraicClosure (K.residueField y)
      let κy : Spec (CommRingCat.of k) ⟶ K :=
        Spec.map (CommRingCat.ofHom (algebraMap (K.residueField y) k)) ≫ K.fromSpecResidueField y
      have hκy : ∀ x, κy.base x = y := fun x => by
        show (K.fromSpecResidueField y).base _ = y; rw [Scheme.fromSpecResidueField_apply]
      let sk : B →+* k := (Spec.preimage (κy ≫ E.L.schemeKerStr N)).hom
      have hsk : geomPoint k sk = κy ≫ E.L.schemeKerStr N := by
        show Spec.map (CommRingCat.ofHom sk) = _; simp [sk]
      have hNk : (N : k) ≠ 0 := by
        have : IsUnit ((N : ℕ) : k) := by simpa using hN.map sk
        exact this.ne_zero
      have hN0 : N ≠ 0 := by rintro rfl; exact hNk (by simp)
      haveI : NeZero N := ⟨hN0⟩

      let A₁ : Set (SchemeHomOver (geomPoint k sk) E.f) := {Q | FactorsThrough (U.ι ≫ ιK) Q}
      let A₂ : Set (SchemeHomOver (geomPoint k sk) E.f) := {Q | FactorsThrough (E''.lev ≫ e''.hom) Q}
      have h12 : A₁ ⊆ A₂ := fun Q hQ => himp _ Q hQ
      obtain ⟨e₁, -⟩ := hlev_fibre k sk hNk
      obtain ⟨e₂, -⟩ := E''.lev_fibre k sk hNk

      let Ψ : ↥A₂ → {Q : SchemeHomOver (geomPoint k sk) E''.f // FactorsThrough E''.lev Q} :=
        fun Q => ⟨mapPt e''.inv (by rw [Iso.inv_comp_eq, he'']) Q.1, (hback _ Q.1).1 Q.2⟩
      have hΨinj : Function.Injective Ψ := by
        intro Q Q' h
        have h1 : Q.1.1 ≫ e''.inv = Q'.1.1 ≫ e''.inv := congrArg (fun z => z.1.1) h
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg (· ≫ e''.hom) h1
      have hfin₂ : A₂.Finite := by
        haveI : Finite {Q : SchemeHomOver (geomPoint k sk) E''.f // FactorsThrough E''.lev Q} :=
          Finite.of_equiv _ e₂
        exact Set.finite_coe_iff.1 (Finite.of_injective Ψ hΨinj)
      have hcard : A₂.ncard ≤ A₁.ncard := by
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
        have hA₁ : Nat.card ↥A₁ = Nat.card (ZMod N × ZMod N) := (Nat.card_congr e₁).symm
        haveI : Finite {Q : SchemeHomOver (geomPoint k sk) E''.f // FactorsThrough E''.lev Q} :=
          Finite.of_equiv _ e₂
        calc Nat.card ↥A₂ ≤ Nat.card {Q : SchemeHomOver (geomPoint k sk) E''.f // FactorsThrough E''.lev Q} :=
              Nat.card_le_card_of_injective Ψ hΨinj
          _ = Nat.card (ZMod N × ZMod N) := (Nat.card_congr e₂).symm
          _ = Nat.card ↥A₁ := hA₁.symm
      have hA : A₁ = A₂ := Set.eq_of_subset_of_ncard_le h12 hcard hfin₂

      let Qy : SchemeHomOver (geomPoint k sk) E.f := ⟨κy ≫ ιK, by rw [Category.assoc, hιKf, hsk]⟩
      have hQy₂ : Qy ∈ A₂ := by
        show FactorsThrough (E''.lev ≫ e''.hom) Qy
        rw [hU''pts]
        refine ⟨κy, rfl, ?_⟩
        rintro _ ⟨x, rfl⟩; rw [hκy]; exact hy
      have hQy₁ : Qy ∈ A₁ := by rw [hA]; exact hQy₂
      obtain ⟨-, hVy⟩ := (F1 _ Qy).1 hQy₁
      have : ιK.base y ∈ V := by
        have hx := hVy ⟨Classical.arbitrary _, rfl⟩
        change ιK.base (κy.base (Classical.arbitrary _)) ∈ V at hx
        rwa [hκy] at hx
      exact (hUV y).2 this

    have hmapL : FactorsThrough E'.lev (mapPt (Iso.refl E.A).inv (by rw [Iso.inv_comp_eq, he]) P) ↔
        FactorsThrough (U.ι ≫ ιK) P := by
      have : mapPt (Iso.refl E.A).inv (by rw [Iso.inv_comp_eq, he]) P = P := Subtype.ext (Category.comp_id _)
      rw [this]
    rw [hmapL, ← hback t P]
    constructor
    · exact himp t P
    · intro hQ
      obtain ⟨κ, hκ, hr⟩ := (hU''pts t P).1 hQ
      refine (F1 t P).2 ⟨(exists_comp_fst_eq_iff_nsmulPt_eq_one E.L t N P).1 ⟨κ, hκ⟩, ?_⟩
      rintro _ ⟨x, rfl⟩
      have h1 : P.1.base x = ιK.base (κ.base x) := by rw [← hκ]; rfl
      rw [h1]
      exact (hUV _).1 (hsup (hr ⟨x, rfl⟩))

end S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_lev_lift
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_lev_lift (solution)
