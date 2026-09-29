-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c8ec3387-0dd5-52b7-a32c-cb464faf9387

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

namespace WFL8

section generic
variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem one_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (L.one t₂).1 = (L.one t₁).1 := by subst h; rfl

theorem nsmulPt_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (n : ℕ)
    (P : SchemeHomOver t₁ f) (P' : SchemeHomOver t₂ f) (hPP' : P'.1 = P.1) :
    (nsmulPt L t₂ n P').1 = (nsmulPt L t₁ n P).1 := by
  subst h
  obtain rfl : P' = P := Subtype.ext hPP'
  rfl

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f)
    (h : L.mul t y y = y) : y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem nsmulPt_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih => simp only [nsmulPt]; rw [L.mul_natural, ih]

end generic

section transport

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
  (hg : IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))

def gpt {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' E'.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f :=
  ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩

@[scoped simp] theorem gpt_coe {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q : SchemeHomOver t' E'.f) :
    (gpt hg t' Q).1 = Q.1 ≫ g := rfl

include hg in
theorem ginj {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (Q Q' : SchemeHomOver t' E'.f)
    (h : Q.1 ≫ g = Q'.1 ≫ g) : Q = Q' :=
  Subtype.ext (hg.hom_ext h (by rw [Q.2, Q'.2]))

variable (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
    (E'.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

include hmul in
theorem gmul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f) :
    gpt hg t' (E'.L.mul t' P Q) = E.L.mul _ (gpt hg t' P) (gpt hg t' Q) := Subtype.ext (hmul t' P Q)

include hmul in
theorem gone {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) : gpt hg t' (E'.L.one t') = E.L.one _ := by
  apply eq_one_of_mul_self
  rw [← gmul hg hmul, E'.L.one_mul]

include hmul in
theorem gnsmul {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (Q : SchemeHomOver t' E'.f) :
    gpt hg t' (nsmulPt E'.L t' n Q) = nsmulPt E.L _ n (gpt hg t' Q) := by
  induction n with
  | zero => exact gone hg hmul t'
  | succ n ih => simp only [nsmulPt]; rw [gmul hg hmul, ih]

theorem gact (hact : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x : ↥Λ) (Q : SchemeHomOver t' E'.f) :
    gpt hg t' (pushPt (E'.act x) (E'.act_over x) Q) = pushPt (E.act x) (E.act_over x) (gpt hg t' Q) := by
  apply Subtype.ext
  simp only [gpt_coe, mapPt_coe, Category.assoc, hact x]

omit hg in
theorem hgeom (k : Type) [Field k] (sk : S' →+* k) :
    geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk.comp φ) := by
  show Spec.map (CommRingCat.ofHom sk) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (sk.comp φ))
  rw [← Spec.map_comp]; rfl

noncomputable def liftP (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) E'.f :=
  ⟨hg.lift (Spec.map (CommRingCat.ofHom φ) ≫ P.1) (𝟙 _)
    (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp]), hg.lift_snd _ _ _⟩

theorem liftP_g (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) :
    (liftP hg P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ P.1 := hg.lift_fst _ _ _

theorem gpt_liftP (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) :
    gpt hg _ (liftP hg P) = GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom φ))
      (by rw [Category.comp_id, Category.id_comp]) P := Subtype.ext (liftP_g hg P)

theorem gsec (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) (k : Type) [Field k] (sk : S' →+* k) :
    (gpt hg _ (FakeEllipticCurve.sectionAt (liftP hg P) k sk)).1 = (FakeEllipticCurve.sectionAt P k (sk.comp φ)).1 := by
  show (geomPoint k sk ≫ (liftP hg P).1) ≫ g = geomPoint k (sk.comp φ) ≫ P.1
  rw [Category.assoc, liftP_g, ← Category.assoc, hgeom]

include hmul in
private theorem _root_.WFL8.torsion (m : ℕ) (PP : E.FullLevel m) :
    nsmulPt E'.L (𝟙 _) m (liftP hg PP.P) = E'.L.one (𝟙 _) := by
  apply ginj hg
  have h1 := congrArg Subtype.val (gnsmul hg hmul (𝟙 _) m (liftP hg PP.P))
  rw [gpt_coe, gpt_liftP, ← nsmulPt_natural, PP.torsion, E.L.one_natural] at h1
  have h2 := congrArg Subtype.val (gone hg hmul (𝟙 (Spec (CommRingCat.of S'))))
  rw [gpt_coe] at h2
  rw [h1, h2]

p2m_export "WFL8" "torsion"
include hmul in
private theorem _root_.WFL8.generates (hact : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x) (m : ℕ) (PP : E.FullLevel m)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (Q : SchemeHomOver (geomPoint k sk) E'.f)
    (hQ : nsmulPt E'.L (geomPoint k sk) m Q = E'.L.one (geomPoint k sk)) :
    ∃ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt (liftP hg PP.P) k sk) = Q := by
  let Qg : SchemeHomOver (geomPoint k (sk.comp φ)) E.f :=
    ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2, hgeom]⟩
  have hQg : nsmulPt E.L (geomPoint k (sk.comp φ)) m Qg = E.L.one _ := by
    apply Subtype.ext
    have h1 := congrArg Subtype.val (gnsmul hg hmul _ m Q)
    rw [hQ, gone hg hmul] at h1
    exact (nsmulPt_coe_congr E.L (hgeom k sk) m (gpt hg _ Q) Qg rfl).trans
      (h1.symm.trans (one_coe_congr E.L (hgeom k sk)).symm)
  obtain ⟨x, hx⟩ := PP.generates k (sk.comp φ) Qg hQg
  refine ⟨x, ginj hg _ _ _ ?_⟩
  have := congrArg Subtype.val hx
  simp only [mapPt_coe] at this ⊢
  rw [← gsec hg PP.P k sk] at this
  simp only [gpt_coe, Category.assoc] at this
  rw [Category.assoc, hact x]
  exact this

p2m_export "WFL8" "generates"
include hmul in
private theorem _root_.WFL8.annihilator (hact : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x) (m : ℕ) (PP : E.FullLevel m)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (x : ↥Λ) :
    pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt (liftP hg PP.P) k sk) = E'.L.one (geomPoint k sk) ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  rw [← PP.annihilator k (sk.comp φ) x]
  constructor
  · intro h
    apply Subtype.ext
    have h1 := congrArg Subtype.val (congrArg (gpt hg _) h)
    rw [gact hg hact, gone hg hmul] at h1
    simp only [mapPt_coe] at h1 ⊢
    rw [gsec hg PP.P k sk] at h1
    rw [one_coe_congr E.L (hgeom k sk)]
    exact h1
  · intro h
    apply ginj hg
    have h1 := congrArg Subtype.val (gact hg hact _ x (FakeEllipticCurve.sectionAt (liftP hg PP.P) k sk))
    have h2 := congrArg Subtype.val (gone hg hmul (geomPoint k sk))
    rw [gpt_coe] at h1 h2
    rw [h1, h2]
    have h3 := congrArg Subtype.val h
    simp only [mapPt_coe] at h3 ⊢
    rw [gsec hg PP.P k sk, h3, one_coe_congr E.L (hgeom k sk)]

p2m_export "WFL8" "annihilator"
end transport

end WFL8
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback.WFL8"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) :
    ∃ u' : FakeEllipticCurve.WithFullLevel Λ N m S', FakeEllipticCurve.WithFullLevel.IsPullback φ u u' := by
  obtain ⟨E, PP⟩ := u
  obtain ⟨E', g, hg, hmul, hact, hlev, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff φ E
  let PL : E'.FullLevel m :=
    ⟨WFL8.liftP hg PP.P, WFL8.torsion hg hmul m PP, WFL8.generates hg hmul hact m PP, WFL8.annihilator hg hmul hact m PP⟩
  exact ⟨⟨E', PL⟩, g, hg, hmul, hact, hlev, WFL8.liftP_g hg PP.P⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback (solution)
