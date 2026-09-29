-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/36456f5d-d852-58a4-a6d3-a31dc47c6779

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace P3FrobRerigid

universe u

section Points

variable {R : Type u} [CommRing R] {A A' A'' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}

theorem mapPt_mapPt (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    (h : (φ ≫ ψ) ≫ f'' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) h P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]

theorem mapPt_congr {φ φ' : A ⟶ A'} (h : φ = φ') (hφ : φ ≫ f' = f) (hφ' : φ' ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by
  subst h; rfl

variable (L : GoodReductionJacobian.RelativeGroupLaw R f)

theorem nsmulPt_zero {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    nsmulPt L t 0 P = L.one t := rfl

theorem nsmulPt_succ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n + 1) P = L.mul t (nsmulPt L t n P) P := rfl

theorem eq_one_of_mul_self_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {x : SchemeHomOver t f}
    (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

end Points

section Act

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
  (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

theorem act_zero (P : SchemeHomOver t E.f) : pushPt (E.act 0) (E.act_over 0) P = E.L.one t := by
  have h := E.act_add 0 0 t P
  rw [add_zero] at h
  exact eq_one_of_mul_self_eq E.L t h.symm

theorem act_nsmul (n : ℕ) (x : ↥Λ) (P : SchemeHomOver t E.f) :
    pushPt (E.act (n • x)) (E.act_over (n • x)) P = nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) P) := by
  induction n with
  | zero => rw [zero_nsmul, nsmulPt_zero]; exact act_zero E t P
  | succ n ih => rw [succ_nsmul, E.act_add, ih, nsmulPt_succ]

theorem act_natCast (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩) (E.act_over _) P = nsmulPt E.L t n P := by
  have he : (⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ : ↥Λ) = n • (⟨1, h1⟩ : ↥Λ) := by
    apply Subtype.ext
    simp [nsmul_eq_mul, QuaternionAlgebra.coe_natCast]
  rw [he, act_nsmul]
  congr 1
  apply Subtype.ext
  simp only [mapPt_coe, E.act_one h1, Category.comp_id]

theorem eq_act_natCast_of_forall (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (g : E.A ⟶ E.A) (hg : g ≫ E.f = E.f)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f), mapPt g hg P = nsmulPt E.L t n P) :
    g = E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ := by
  have h' := h E.f ⟨𝟙 _, Category.id_comp _⟩
  rw [← act_natCast E E.f h1 n hn] at h'
  have := congrArg Subtype.val h'
  simpa only [mapPt_coe, Category.id_comp] using this

end Act

end P3FrobRerigid

open P3FrobRerigid GoodReductionJacobian CerednikDrinfeld.QM.FakeEllipticCurve in
theorem solution
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (σ : Onr →ₐ[𝒪] Onr)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π σ) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f) (V : A₀r.A ⟶ A₀.A) (hV : V ≫ A₀.f = A₀r.f)
    (F_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
      mapPt F hF (A₀.L.mul t P Q) = A₀r.L.mul t (mapPt F hF P) (mapPt F hF Q))
    (V_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀r.f),
      mapPt V hV (A₀r.L.mul t P Q) = A₀.L.mul t (mapPt V hV P) (mapPt V hV Q))
    (F_act : ∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x) (V_act : ∀ x : ↥Λ, A₀r.act x ≫ V = V ≫ A₀.act x)
    (F_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev P → FactorsThrough A₀r.lev (mapPt F hF P))
    (V_F : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      mapPt V hV (mapPt F hF P) = nsmulPt A₀.L t r P)
    (F_V : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
      mapPt F hF (mapPt V hV Q) = nsmulPt A₀r.L t r Q) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B)
      (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E),
      ∃ (ρp : FakeEllipticCurve.Rigidification r π A₀ (ψ.comp σ) E)
        (ub : ρ.Eb.A ⟶ ρp.Eb.A) (_ : ub ≫ ρp.gb = ρ.gb) (_ : ub ≫ ρp.Eb.f = ρ.Eb.f)
        (gA' : ρp.Ab.A ⟶ A₀r.A) (_ : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρp.Ab gA')
        (_ : gA' ≫ prA = ρp.gA)
        (Fb : ρ.Ab.A ⟶ ρp.Ab.A) (_ : Fb ≫ gA' = ρ.gA ≫ F) (_ : Fb ≫ ρp.Ab.f = ρ.Ab.f)
        (Vb : ρp.Ab.A ⟶ ρ.Ab.A) (_ : Vb ≫ ρ.gA = gA' ≫ V) (_ : Vb ≫ ρ.Ab.f = ρp.Ab.f),
        ρp.d = ρ.d + 1 ∧ ub ≫ ρp.φ = ρ.φ ≫ Fb ∧ ρp.φ' = Vb ≫ ρ.φ' ≫ ub := by
  intro B _ _ ψ E ρ

  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hr : (((r : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ (r : ℕ)
  have hrd : (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ (r ^ ρ.d : ℕ)
  have hrd1 : (((r ^ (ρ.d + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ (r ^ (ρ.d + 1) : ℕ)
  set χ := FakeEllipticCurve.Rigidification.residueLeg π ψ with hχdef
  set Frb := FakeEllipticCurve.Rigidification.residueLeg π σ with hFrbdef

  have hχp : FakeEllipticCurve.Rigidification.residueLeg π (ψ.comp σ) = χ.comp Frb := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp [hχdef, hFrbdef, FakeEllipticCurve.Rigidification.residueLeg, Ideal.quotientMap_mk]

  have hFV : F ≫ V = A₀.act ⟨_, hr⟩ :=
    eq_act_natCast_of_forall A₀ h1 r hr (F ≫ V) (by rw [Category.assoc, hV, hF])
      (fun t P => by rw [← mapPt_mapPt F hF V hV, V_F])
  have hVF : V ≫ F = A₀r.act ⟨_, hr⟩ :=
    eq_act_natCast_of_forall A₀r h1 r hr (V ≫ F) (by rw [Category.assoc, hF, hV])
      (fun t P => by rw [← mapPt_mapPt V hV F hF, F_V])

  obtain ⟨hρA, hρA_mul, hρA_act, hρA_lev⟩ := ρ.isPullback_Ab
  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := ρ.isIsogenyPair
  obtain ⟨hφφ', hφ'φ⟩ := hdeg hrd
  obtain ⟨hprA_sq, hprA_mul, hprA_act, hprA_lev⟩ := hprA

  obtain ⟨Ab', gA', hg', hmul', hact', hlev', hlev''⟩ := FakeEllipticCurve.exists_isPullback_levelIff χ A₀r

  have wF : (ρ.gA ≫ F) ≫ A₀r.f = ρ.Ab.f ≫ Spec.map (CommRingCat.ofHom χ) := by
    rw [Category.assoc, hF]; exact hρA.w
  let Fb : ρ.Ab.A ⟶ Ab'.A := hg'.lift (ρ.gA ≫ F) ρ.Ab.f wF
  have hFb₁ : Fb ≫ gA' = ρ.gA ≫ F := hg'.lift_fst _ _ _
  have hFb₂ : Fb ≫ Ab'.f = ρ.Ab.f := hg'.lift_snd _ _ _
  have wV : (gA' ≫ V) ≫ A₀.f = Ab'.f ≫ Spec.map (CommRingCat.ofHom χ) := by
    rw [Category.assoc, hV]; exact hg'.w
  let Vb : Ab'.A ⟶ ρ.Ab.A := hρA.lift (gA' ≫ V) Ab'.f wV
  have hVb₁ : Vb ≫ ρ.gA = gA' ≫ V := hρA.lift_fst _ _ _
  have hVb₂ : Vb ≫ ρ.Ab.f = Ab'.f := hρA.lift_snd _ _ _

  have hFbVb : Fb ≫ Vb = ρ.Ab.act ⟨_, hr⟩ := by
    apply hρA.hom_ext
    · rw [Category.assoc, hVb₁, ← Category.assoc, hFb₁, Category.assoc, hFV, hρA_act]
    · rw [Category.assoc, hVb₂, hFb₂, ρ.Ab.act_over]
  have hVbFb : Vb ≫ Fb = Ab'.act ⟨_, hr⟩ := by
    apply hg'.hom_ext
    · rw [Category.assoc, hFb₁, ← Category.assoc, hVb₁, Category.assoc, hVF, hact']
    · rw [Category.assoc, hFb₂, hVb₂, Ab'.act_over]

  have hFb_act : ∀ x : ↥Λ, ρ.Ab.act x ≫ Fb = Fb ≫ Ab'.act x := by
    intro x
    apply hg'.hom_ext
    · rw [Category.assoc, hFb₁, ← Category.assoc, hρA_act, Category.assoc, F_act, Category.assoc, hact',
        ← Category.assoc Fb gA', hFb₁, Category.assoc]
    · rw [Category.assoc, hFb₂, ρ.Ab.act_over, Category.assoc, Ab'.act_over, hFb₂]
  have hVb_act : ∀ x : ↥Λ, Ab'.act x ≫ Vb = Vb ≫ ρ.Ab.act x := by
    intro x
    apply hρA.hom_ext
    · rw [Category.assoc, hVb₁, ← Category.assoc, hact', Category.assoc, V_act, Category.assoc, hρA_act,
        ← Category.assoc Vb ρ.gA, hVb₁, Category.assoc]
    · rw [Category.assoc, hVb₂, Ab'.act_over, Category.assoc, ρ.Ab.act_over, hVb₂]

  have ptext : ∀ {S₁ : Type} [CommRing S₁] {X Y Z : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of S₁)} {g : X ⟶ Y} {fY : Y ⟶ Z}
      {s : Spec (CommRingCat.of S₁) ⟶ Z} (hsq : CategoryTheory.IsPullback g fX fY s)
      {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S₁)} (P Q : SchemeHomOver t fX), P.1 ≫ g = Q.1 ≫ g → P = Q := by
    intro S₁ _ X Y Z fX g fY s hsq T t P Q h
    exact Subtype.ext (hsq.hom_ext h (by rw [P.2, Q.2]))

  have hFb_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P Q : SchemeHomOver t ρ.Ab.f), mapPt Fb hFb₂ (ρ.Ab.L.mul t P Q) = Ab'.L.mul t (mapPt Fb hFb₂ P) (mapPt Fb hFb₂ Q) := by
    intro T t P Q
    apply ptext hg'
    rw [mapPt_coe, Category.assoc, hFb₁, ← Category.assoc, hρA_mul, hmul']
    have := congrArg Subtype.val (F_hom (t ≫ Spec.map (CommRingCat.ofHom χ))
      ⟨P.1 ≫ ρ.gA, by rw [Category.assoc, hρA.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ ρ.gA, by rw [Category.assoc, hρA.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr A₀r.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hFb₁])
      (by simp only [mapPt_coe, Category.assoc, hFb₁])
  have hVb_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
      (P Q : SchemeHomOver t Ab'.f), mapPt Vb hVb₂ (Ab'.L.mul t P Q) = ρ.Ab.L.mul t (mapPt Vb hVb₂ P) (mapPt Vb hVb₂ Q) := by
    intro T t P Q
    apply ptext hρA
    rw [mapPt_coe, Category.assoc, hVb₁, ← Category.assoc, hmul', hρA_mul]
    have := congrArg Subtype.val (V_hom (t ≫ Spec.map (CommRingCat.ofHom χ))
      ⟨P.1 ≫ gA', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
      ⟨Q.1 ≫ gA', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩)
    rw [mapPt_coe] at this
    rw [this]
    exact mul_val_congr A₀.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hVb₁])
      (by simp only [mapPt_coe, Category.assoc, hVb₁])

  have hpaste : FakeEllipticCurve.IsPullbackVia (χ.comp Frb) A₀ Ab' (gA' ≫ prA) := by
    have hsq : CategoryTheory.IsPullback (gA' ≫ prA) Ab'.f A₀.f (Spec.map (CommRingCat.ofHom (χ.comp Frb))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      exact hg'.paste_horiz hprA_sq
    refine ⟨hsq, ?_, ?_, ?_⟩
    · intro T t' P Q
      rw [← Category.assoc, hmul', hprA_mul]
      exact mul_val_congr A₀.L (by rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]) _ _ _ _
        (by simp only [Category.assoc]) (by simp only [Category.assoc])
    · intro x
      rw [← Category.assoc, hact', Category.assoc, hprA_act, Category.assoc]
    · intro T t' P hP
      obtain ⟨P₀, hP₀⟩ := hlev' t' P hP
      obtain ⟨P₁, hP₁⟩ := hprA_lev (t' ≫ Spec.map (CommRingCat.ofHom χ))
        ⟨P.1 ≫ gA', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
      exact ⟨P₁, by rw [hP₁, Category.assoc]⟩

  refine ⟨{ Eb := ρ.Eb, gb := ρ.gb, isPullback_Eb := ρ.isPullback_Eb, Ab := Ab', gA := gA' ≫ prA,
            isPullback_Ab := ?_, d := ρ.d + 1, φ := ρ.φ ≫ Fb, φ' := Vb ≫ ρ.φ',
            φ_over := by rw [Category.assoc, hFb₂, hφo], isIsogenyPair := ?_, preservesLevel := ?_ },
          𝟙 _, Category.id_comp _, Category.id_comp _, gA', ⟨hg', hmul', hact', hlev'⟩, rfl,
          Fb, hFb₁, hFb₂, Vb, hVb₁, hVb₂, rfl, Category.id_comp _, ?_⟩
  ·
    show FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (ψ.comp σ)) A₀ Ab' (gA' ≫ prA)
    rw [hχp]; exact hpaste
  ·
    refine ⟨by rw [Category.assoc, hFb₂, hφo], by rw [Category.assoc, hφ'o, hVb₂], ?_, ?_, ?_, ?_, ?_⟩
    · intro T t P Q
      rw [← mapPt_mapPt ρ.φ hφo Fb hFb₂, ← mapPt_mapPt ρ.φ hφo Fb hFb₂, ← mapPt_mapPt ρ.φ hφo Fb hFb₂, hφmul, hFb_hom]
    · intro T t P Q
      rw [← mapPt_mapPt Vb hVb₂ ρ.φ' hφ'o, ← mapPt_mapPt Vb hVb₂ ρ.φ' hφ'o, ← mapPt_mapPt Vb hVb₂ ρ.φ' hφ'o, hVb_hom, hφ'mul]
    · intro x; rw [← Category.assoc, hφlin, Category.assoc, hFb_act, Category.assoc]
    · intro x; rw [← Category.assoc, hVb_act, Category.assoc, hφ'lin, Category.assoc]
    · intro hd
      have e1 : (⟨_, hd⟩ : ↥Λ) = ⟨(((r : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]),
          by have := hd; push_cast at this ⊢; rwa [pow_succ'] at this⟩ := by
        apply Subtype.ext
        show (((r ^ (ρ.d + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) = _
        push_cast; exact pow_succ' _ _
      have e2 : (⟨_, hd⟩ : ↥Λ) = ⟨(((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (((r : ℕ) : ℚ) : ℍ[ℚ, a, b]),
          by have := hd; push_cast at this ⊢; rwa [pow_succ] at this⟩ := by
        apply Subtype.ext
        show (((r ^ (ρ.d + 1) : ℕ) : ℚ) : ℍ[ℚ, a, b]) = _
        push_cast; exact pow_succ _ _
      constructor
      · rw [Category.assoc, ← Category.assoc Fb, hFbVb, ← Category.assoc, Category.assoc ρ.φ, hφ'lin, ← Category.assoc, hφφ',
          e1, ρ.Eb.act_mul ⟨_, hr⟩ ⟨_, hrd⟩]
      · rw [Category.assoc, ← Category.assoc ρ.φ', hφ'φ, ← Category.assoc, Category.assoc Vb, hFb_act, ← Category.assoc, hVbFb,
          e2, Ab'.act_mul ⟨_, hrd⟩ ⟨_, hr⟩]
  ·
    intro T t P hP
    rw [← mapPt_mapPt ρ.φ hφo Fb hFb₂]
    have hQ := ρ.preservesLevel t P hP
    apply hlev''
    obtain ⟨P₀, hP₀⟩ := hρA_lev t _ hQ
    obtain ⟨P₁, hP₁⟩ := F_lev (t ≫ Spec.map (CommRingCat.ofHom χ))
      ⟨(mapPt ρ.φ hφo P).1 ≫ ρ.gA, by rw [Category.assoc, hρA.w, ← Category.assoc, (mapPt ρ.φ hφo P).2]⟩ ⟨P₀, hP₀⟩
    refine ⟨P₁, ?_⟩
    rw [hP₁]
    simp only [mapPt_coe, Category.assoc, hFb₁]
  ·
    show Vb ≫ ρ.φ' = Vb ≫ ρ.φ' ≫ 𝟙 _
    rw [Category.comp_id]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_comp_of_isPullbackVia_residueLeg_of_isogenyPair (solution)
