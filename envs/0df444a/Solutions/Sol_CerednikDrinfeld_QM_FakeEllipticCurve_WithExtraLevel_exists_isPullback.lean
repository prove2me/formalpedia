-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2548587a-de78-566f-824d-c7b69d827697

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_AlgebraicGeometry_isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw
open CerednikDrinfeld.QM

namespace PullbackExists

variable {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')

theorem bundle_baseChange {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f) (L : RelativeGroupLaw S f) :
    AbelianSchemePropertyBundle S' (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) where
  smooth := by haveI := hA.smooth; infer_instance
  proper := by haveI := hA.proper; infer_instance
  connectedFibres := by
    intro s'
    apply isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed
    intro k _ _ t
    have hB := hA.baseChange_of_field (t ≫ (Spec.map (CommRingCat.ofHom φ)))
    haveI : IsIntegral (pullback f (t ≫ (Spec.map (CommRingCat.ofHom φ)))) := hB.isIntegral_of_field
    haveI : IsIntegral (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) t) :=
      IsIntegral.of_isIso (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom φ)) t).inv
    infer_instance
  hasGroupLaw := ⟨L.baseChange (Spec.map (CommRingCat.ofHom φ))⟩

theorem baseChange_mul_coe_fst {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))) :
    ((L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom φ)) =
      (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom φ))) (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P) (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) Q)).1 := by
  have h := congrArg Subtype.val (baseChangePointToBase_mul (Spec.map (CommRingCat.ofHom φ)) L t' P Q)
  rwa [baseChangePointToBase_coe] at h

section Act

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

noncomputable def act' (a : A ⟶ A) (ha : a ≫ f = f) : pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ pullback f (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ≫ a) (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (by rw [Category.assoc, ha, pullback.condition])

@[scoped simp] theorem act'_fst (a : A ⟶ A) (ha : a ≫ f = f) :
    act' φ a ha ≫ pullback.fst f (Spec.map (CommRingCat.ofHom φ)) = pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ≫ a := pullback.lift_fst _ _ _

@[scoped simp] theorem act'_over (a : A ⟶ A) (ha : a ≫ f = f) :
    act' φ a ha ≫ pullback.snd f (Spec.map (CommRingCat.ofHom φ)) = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) := pullback.lift_snd _ _ _

theorem baseChangePointToBase_pushPt (a : A ⟶ A) (ha : a ≫ f = f)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))) :
    baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) (pushPt (act' φ a ha) (act'_over φ a ha) P) =
      pushPt a ha (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P) := by
  apply Subtype.ext
  simp only [baseChangePointToBase_coe, mapPt_coe, Category.assoc, act'_fst]

theorem act'_id (a : A ⟶ A) (ha : a ≫ f = f) (h : a = 𝟙 A) : act' φ a ha = 𝟙 _ := by
  subst h
  apply pullback.hom_ext
  · rw [act'_fst, Category.id_comp, Category.comp_id]
  · rw [act'_over, Category.id_comp]

theorem act'_comp (a b c : A ⟶ A) (ha : a ≫ f = f) (hb : b ≫ f = f) (hc : c ≫ f = f) (h : c = b ≫ a) :
    act' φ c hc = act' φ b hb ≫ act' φ a ha := by
  subst h
  apply pullback.hom_ext
  · rw [act'_fst, Category.assoc, act'_fst, ← Category.assoc (act' φ b hb), act'_fst, Category.assoc]
  · rw [act'_over, Category.assoc, act'_over, act'_over]

theorem act'_hom (L : RelativeGroupLaw S f) (a : A ⟶ A) (ha : a ≫ f = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt a ha (L.mul t P Q) = L.mul t (pushPt a ha P) (pushPt a ha Q))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))) :
    pushPt (act' φ a ha) (act'_over φ a ha) ((L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' P Q) =
      (L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' (pushPt (act' φ a ha) (act'_over φ a ha) P)
        (pushPt (act' φ a ha) (act'_over φ a ha) Q) := by
  apply (baseChangePointEquiv (Spec.map (CommRingCat.ofHom φ)) t').injective
  show baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _ = baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _
  rw [baseChangePointToBase_pushPt, baseChangePointToBase_mul, hhom, baseChangePointToBase_mul,
    baseChangePointToBase_pushPt, baseChangePointToBase_pushPt]

theorem act'_add (L : RelativeGroupLaw S f) (a b c : A ⟶ A) (ha : a ≫ f = f) (hb : b ≫ f = f) (hc : c ≫ f = f)
    (hadd : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      pushPt c hc P = L.mul t (pushPt a ha P) (pushPt b hb P))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))) :
    pushPt (act' φ c hc) (act'_over φ c hc) P =
      (L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' (pushPt (act' φ a ha) (act'_over φ a ha) P)
        (pushPt (act' φ b hb) (act'_over φ b hb) P) := by
  apply (baseChangePointEquiv (Spec.map (CommRingCat.ofHom φ)) t').injective
  show baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _ = baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _
  rw [baseChangePointToBase_pushPt, hadd, baseChangePointToBase_mul, baseChangePointToBase_pushPt,
    baseChangePointToBase_pushPt]

end Act

section FEC

open scoped Quaternion
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem fec_bundle (E : FakeEllipticCurve Λ N S) :
    AbelianSchemePropertyBundle S' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) := bundle_baseChange φ E.bundle E.L

theorem fec_comm (E : FakeEllipticCurve Λ N S) : (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).IsCommutative :=
  RelativeGroupLaw.IsCommutative.baseChange (Spec.map (CommRingCat.ofHom φ)) (G := E.L) E.comm

theorem fec_act_hom (E : FakeEllipticCurve Λ N S) (x : ↥Λ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    pushPt (act' φ (E.act x) (E.act_over x)) (act'_over φ _ _) ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' P Q) =
      (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' (pushPt (act' φ (E.act x) (E.act_over x)) (act'_over φ _ _) P)
        (pushPt (act' φ (E.act x) (E.act_over x)) (act'_over φ _ _) Q) :=
  act'_hom φ E.L (E.act x) (E.act_over x) (E.act_hom x) t' P Q

theorem fec_act_one (E : FakeEllipticCurve Λ N S) (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) :
    act' φ (E.act ⟨1, h⟩) (E.act_over _) = 𝟙 _ := act'_id φ _ _ (E.act_one h)

theorem fec_act_mul (E : FakeEllipticCurve Λ N S) (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    act' φ (E.act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩) (E.act_over _) =
      act' φ (E.act y) (E.act_over y) ≫ act' φ (E.act x) (E.act_over x) :=
  act'_comp φ _ _ _ _ _ _ (E.act_mul x y h)

theorem fec_act_add (E : FakeEllipticCurve Λ N S) (x y : ↥Λ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    pushPt (act' φ (E.act (x + y)) (E.act_over (x + y))) (act'_over φ _ _) P =
      (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' (pushPt (act' φ (E.act x) (E.act_over x)) (act'_over φ _ _) P)
        (pushPt (act' φ (E.act y) (E.act_over y)) (act'_over φ _ _) P) :=
  act'_add φ E.L _ _ _ _ _ _ (fun t Q => E.act_add x y t Q) t' P

theorem fec_mul_compat (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom φ)) =
      (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom φ)))
        ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom φ)), by rw [Category.assoc, (IsPullback.of_hasPullback E.f (Spec.map (CommRingCat.ofHom φ))).w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom φ)), by rw [Category.assoc, (IsPullback.of_hasPullback E.f (Spec.map (CommRingCat.ofHom φ))).w, ← Category.assoc, Q.2]⟩).1 :=
  baseChange_mul_coe_fst φ E.L t' P Q

end FEC

section Level

variable {A C : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (lev : C ⟶ A)

noncomputable def levBC : pullback (lev ≫ f) (Spec.map (CommRingCat.ofHom φ)) ⟶ pullback f (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift (pullback.fst (lev ≫ f) (Spec.map (CommRingCat.ofHom φ)) ≫ lev) (pullback.snd (lev ≫ f) (Spec.map (CommRingCat.ofHom φ)))
    (by rw [Category.assoc, pullback.condition])

@[scoped simp] theorem levBC_snd : levBC φ f lev ≫ pullback.snd f (Spec.map (CommRingCat.ofHom φ)) = pullback.snd (lev ≫ f) (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift_snd _ _ _

@[scoped simp] theorem levBC_fst : levBC φ f lev ≫ pullback.fst f (Spec.map (CommRingCat.ofHom φ)) = pullback.fst (lev ≫ f) (Spec.map (CommRingCat.ofHom φ)) ≫ lev :=
  pullback.lift_fst _ _ _

theorem isPullback_levBC : IsPullback (pullback.fst (lev ≫ f) (Spec.map (CommRingCat.ofHom φ))) (levBC φ f lev) lev (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (v₂₂ := f) (h₃₁ := (Spec.map (CommRingCat.ofHom φ))) ?_ (levBC_fst φ f lev).symm
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ)))
  rw [levBC_snd]
  exact IsPullback.of_hasPullback (lev ≫ f) (Spec.map (CommRingCat.ofHom φ))

theorem isClosedImmersion_levBC [IsClosedImmersion lev] : IsClosedImmersion (levBC φ f lev) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_levBC φ f lev) inferInstance

scoped instance levBC_comp_isFinite [IsFinite (lev ≫ f)] : IsFinite (levBC φ f lev ≫ pullback.snd f (Spec.map (CommRingCat.ofHom φ))) := by
  rw [levBC_snd]; infer_instance

scoped instance levBC_comp_flat [Flat (lev ≫ f)] : Flat (levBC φ f lev ≫ pullback.snd f (Spec.map (CommRingCat.ofHom φ))) := by
  rw [levBC_snd]; infer_instance

scoped instance levBC_comp_lofp [LocallyOfFinitePresentation (lev ≫ f)] :
    LocallyOfFinitePresentation (levBC φ f lev ≫ pullback.snd f (Spec.map (CommRingCat.ofHom φ))) := by
  rw [levBC_snd]; infer_instance

theorem finrank_levBC [IsFinite (lev ≫ f)] [Flat (lev ≫ f)] (N : ℕ)
    (hrank : ∀ s : ↥(Spec (CommRingCat.of S)), (lev ≫ f).finrank s = N ^ 2) (s' : ↥(Spec (CommRingCat.of S'))) :
    (levBC φ f lev ≫ pullback.snd f (Spec.map (CommRingCat.ofHom φ))).finrank s' = N ^ 2 := by
  rw [levBC_snd, Scheme.Hom.finrank_pullback_snd, hrank]

theorem factorsThrough_iff {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))) :
    FactorsThrough (levBC φ f lev) P ↔ FactorsThrough lev (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P) := by
  constructor
  · rintro ⟨P₀, hP₀⟩
    refine ⟨P₀ ≫ pullback.fst (lev ≫ f) (Spec.map (CommRingCat.ofHom φ)), ?_⟩
    rw [baseChangePointToBase_coe, ← hP₀, Category.assoc, Category.assoc, levBC_fst]
  · rintro ⟨P₀, hP₀⟩
    refine ⟨pullback.lift P₀ (P.1 ≫ pullback.snd f (Spec.map (CommRingCat.ofHom φ)))
      (by rw [← Category.assoc, hP₀, baseChangePointToBase_coe, Category.assoc, Category.assoc, pullback.condition]), ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, levBC_fst, ← Category.assoc, pullback.lift_fst, hP₀, baseChangePointToBase_coe]
    · rw [Category.assoc, levBC_snd, pullback.lift_snd]

theorem baseChangePointToBase_nsmulPt (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (n : ℕ) (P : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))) :
    baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) (nsmulPt (L.baseChange (Spec.map (CommRingCat.ofHom φ))) t' n P) =
      nsmulPt L (t' ≫ (Spec.map (CommRingCat.ofHom φ))) n (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P) := by
  induction n with
  | zero => exact baseChangePointToBase_one (Spec.map (CommRingCat.ofHom φ)) L t'
  | succ n ih =>
    show baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) ((L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' (nsmulPt (L.baseChange (Spec.map (CommRingCat.ofHom φ))) t' n P) P) =
      L.mul _ (nsmulPt L _ n (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P)) (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P)
    rw [baseChangePointToBase_mul, ih]

def rebase {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂) (P : SchemeHomOver t₁ f) :
    SchemeHomOver t₂ f := ⟨P.1, P.2.trans h⟩

@[scoped simp] theorem rebase_coe {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂) (P : SchemeHomOver t₁ f) :
    (rebase f h P).1 = P.1 := rfl

theorem rebase_mul (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) : rebase f h (L.mul t₁ P Q) = L.mul t₂ (rebase f h P) (rebase f h Q) := by
  subst h; rfl

theorem rebase_one (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂) :
    rebase f h (L.one t₁) = L.one t₂ := by
  subst h; rfl

theorem geomPoint_comp (k : Type u) [Field k] (sk' : S' →+* k) :
    geomPoint k sk' ≫ (Spec.map (CommRingCat.ofHom φ)) = geomPoint k (sk'.comp φ) := by
  rw [geomPoint, geomPoint, ← Spec.map_comp]; rfl

theorem tangentBase_comp (k : Type u) [Field k] (sk' : S' →+* k) :
    tangentBase k sk' ≫ (Spec.map (CommRingCat.ofHom φ)) = tangentBase k (sk'.comp φ) := by
  rw [tangentBase, tangentBase, ← Spec.map_comp]; rfl

theorem tangentZero_tangentBase {R₁ : Type u} [CommRing R₁] (k : Type u) [Field k] (sk : R₁ →+* k) :
    tangentZero k ≫ tangentBase k sk = geomPoint k sk := by
  have h : CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp sk) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom = CommRingCat.ofHom sk := by
    ext r; first | rfl | simp
  rw [tangentZero, tangentBase, geomPoint, ← Spec.map_comp, h]

end Level

section LevelFEC

open scoped Quaternion
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem fec_lev_closed (E : FakeEllipticCurve Λ N S) : IsClosedImmersion (levBC φ E.f E.lev) :=
  haveI := E.lev_closed; isClosedImmersion_levBC φ E.f E.lev

theorem fec_lev_sub (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    FactorsThrough (levBC φ E.f E.lev) P → FactorsThrough (levBC φ E.f E.lev) Q →
      FactorsThrough (levBC φ E.f E.lev) ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' P Q) ∧
      FactorsThrough (levBC φ E.f E.lev) ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).inv t' P) := by
  intro hP hQ
  rw [factorsThrough_iff] at hP hQ
  rw [factorsThrough_iff, factorsThrough_iff, baseChangePointToBase_mul, baseChangePointToBase_inv]
  exact E.lev_sub _ _ _ hP hQ

theorem fec_lev_one (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    FactorsThrough (levBC φ E.f E.lev) ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).one t') := by
  rw [factorsThrough_iff, baseChangePointToBase_one]
  exact E.lev_one _

theorem fec_lev_torsion (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    FactorsThrough (levBC φ E.f E.lev) P → nsmulPt (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))) t' N P = (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).one t' := by
  intro hP
  rw [factorsThrough_iff] at hP
  apply (baseChangePointEquiv (Spec.map (CommRingCat.ofHom φ)) t').injective
  show baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _ = baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _
  rw [baseChangePointToBase_nsmulPt, baseChangePointToBase_one]
  exact E.lev_torsion _ _ hP

theorem fec_lev_stable (E : FakeEllipticCurve Λ N S) (x : ↥Λ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    FactorsThrough (levBC φ E.f E.lev) P →
      FactorsThrough (levBC φ E.f E.lev) (pushPt (act' φ (E.act x) (E.act_over x)) (act'_over φ _ _) P) := by
  intro hP
  rw [factorsThrough_iff] at hP
  rw [factorsThrough_iff, baseChangePointToBase_pushPt]
  exact E.lev_stable x _ _ hP

theorem fec_lev_finite (E : FakeEllipticCurve Λ N S) : IsFinite (levBC φ E.f E.lev ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) :=
  haveI := E.lev_finite; inferInstance

theorem fec_lev_flat (E : FakeEllipticCurve Λ N S) : Flat (levBC φ E.f E.lev ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) :=
  haveI := E.lev_flat; inferInstance

theorem fec_lev_fp (E : FakeEllipticCurve Λ N S) :
    LocallyOfFinitePresentation (levBC φ E.f E.lev ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) :=
  haveI := E.lev_finitePresentation; inferInstance

theorem fec_lev_rank (E : FakeEllipticCurve Λ N S) (s' : ↥(Spec (CommRingCat.of S'))) :
    (levBC φ E.f E.lev ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))).finrank s' = N ^ 2 :=
  haveI := E.lev_finite; haveI := E.lev_flat; finrank_levBC φ E.f E.lev N E.lev_rank s'

theorem factorsThrough_rebase {A C : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (lev : C ⟶ A) {T : Scheme.{u}}
    {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂) (P : SchemeHomOver t₁ f) :
    FactorsThrough lev (rebase f h P) ↔ FactorsThrough lev P := by
  subst h; exact Iff.rfl

noncomputable def levPtToBase (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk' : S' →+* k)
    (P : {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) // FactorsThrough (levBC φ E.f E.lev) P}) :
    {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough E.lev P} :=
  ⟨rebase E.f (geomPoint_comp φ k sk') (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P.1),
    (factorsThrough_rebase E.lev (geomPoint_comp φ k sk') _).mpr ((factorsThrough_iff φ E.f E.lev _ P.1).mp P.2)⟩

noncomputable def levPtOfBase (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk' : S' →+* k)
    (Q : {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough E.lev P}) :
    {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) // FactorsThrough (levBC φ E.f E.lev) P} :=
  ⟨baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm Q.1), by
    rw [factorsThrough_iff, baseChangePointToBase_ofBase, factorsThrough_rebase]; exact Q.2⟩

theorem rebase_symm_rebase {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) {T : Scheme.{u}}
    {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂) (P : SchemeHomOver t₁ f) : rebase f h.symm (rebase f h P) = P := by
  subst h; rfl

theorem rebase_rebase_symm {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) {T : Scheme.{u}}
    {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂) (Q : SchemeHomOver t₂ f) : rebase f h (rebase f h.symm Q) = Q := by
  subst h; rfl

theorem levPtOfBase_toBase (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk' : S' →+* k)
    (P : {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) // FactorsThrough (levBC φ E.f E.lev) P}) :
    levPtOfBase φ E k sk' (levPtToBase φ E k sk' P) = P := by
  apply Subtype.ext
  show baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm
    (rebase E.f (geomPoint_comp φ k sk') (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P.1))) = P.1
  rw [rebase_symm_rebase, baseChangePointOfBase_toBase]

theorem levPtToBase_ofBase (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk' : S' →+* k)
    (Q : {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough E.lev P}) :
    levPtToBase φ E k sk' (levPtOfBase φ E k sk' Q) = Q := by
  apply Subtype.ext
  show rebase E.f (geomPoint_comp φ k sk') (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ))
    (baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm Q.1))) = Q.1
  rw [baseChangePointToBase_ofBase, rebase_rebase_symm]

noncomputable def levPtEquiv (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk' : S' →+* k) :
    {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) // FactorsThrough (levBC φ E.f E.lev) P} ≃
    {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough E.lev P} :=
  ⟨levPtToBase φ E k sk', levPtOfBase φ E k sk', levPtOfBase_toBase φ E k sk', levPtToBase_ofBase φ E k sk'⟩

theorem levPtOfBase_mul (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk' : S' →+* k)
    (Q R : {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough E.lev P})
    (QR : {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough E.lev P})
    (h : QR.1 = E.L.mul (geomPoint k (sk'.comp φ)) Q.1 R.1) :
    (levPtOfBase φ E k sk' QR).1 =
      (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul (geomPoint k sk') (levPtOfBase φ E k sk' Q).1 (levPtOfBase φ E k sk' R).1 := by
  show baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm QR.1) =
    (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul (geomPoint k sk')
      (baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm Q.1))
      (baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm R.1))
  rw [baseChange_mul, baseChangePointToBase_ofBase, baseChangePointToBase_ofBase, ← rebase_mul, ← h]

theorem fec_lev_fibre (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] [IsAlgClosed k] (sk' : S' →+* k)
    (hN : (N : k) ≠ 0) :
    ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) //
        FactorsThrough (levBC φ E.f E.lev) P},
      ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) =
        (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul (geomPoint k sk') (e x) (e y) := by
  obtain ⟨e₀, he₀⟩ := E.lev_fibre k (sk'.comp φ) hN
  exact ⟨e₀.trans (levPtEquiv φ E k sk').symm, fun x y =>
    levPtOfBase_mul φ E k sk' (e₀ x) (e₀ y) (e₀ (x + y)) (he₀ x y)⟩

end LevelFEC

section LevelK

open scoped Quaternion
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {ℓ : ℕ}

theorem fec_levK_closed (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) : IsClosedImmersion (levBC φ E.f KK.levK) :=
  haveI := KK.levK_closed; isClosedImmersion_levBC φ E.f KK.levK

theorem fec_levK_sub (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    FactorsThrough (levBC φ E.f KK.levK) P → FactorsThrough (levBC φ E.f KK.levK) Q →
      FactorsThrough (levBC φ E.f KK.levK) ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' P Q) ∧
      FactorsThrough (levBC φ E.f KK.levK) ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).inv t' P) := by
  intro hP hQ
  rw [factorsThrough_iff] at hP hQ
  rw [factorsThrough_iff, factorsThrough_iff, baseChangePointToBase_mul, baseChangePointToBase_inv]
  exact KK.levK_sub _ _ _ hP hQ

theorem fec_levK_one (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    FactorsThrough (levBC φ E.f KK.levK) ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).one t') := by
  rw [factorsThrough_iff, baseChangePointToBase_one]
  exact KK.levK_one _

theorem fec_levK_torsion (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    FactorsThrough (levBC φ E.f KK.levK) P → nsmulPt (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))) t' ℓ P = (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).one t' := by
  intro hP
  rw [factorsThrough_iff] at hP
  apply (baseChangePointEquiv (Spec.map (CommRingCat.ofHom φ)) t').injective
  show baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _ = baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _
  rw [baseChangePointToBase_nsmulPt, baseChangePointToBase_one]
  exact KK.levK_torsion _ _ hP

theorem fec_levK_stable (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) (x : ↥Λ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    FactorsThrough (levBC φ E.f KK.levK) P →
      FactorsThrough (levBC φ E.f KK.levK) (pushPt (act' φ (E.act x) (E.act_over x)) (act'_over φ _ _) P) := by
  intro hP
  rw [factorsThrough_iff] at hP
  rw [factorsThrough_iff, baseChangePointToBase_pushPt]
  exact KK.levK_stable x _ _ hP

theorem fec_levK_finite (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) : IsFinite (levBC φ E.f KK.levK ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) :=
  haveI := KK.levK_finite; inferInstance

theorem fec_levK_flat (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) : Flat (levBC φ E.f KK.levK ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) :=
  haveI := KK.levK_flat; inferInstance

theorem fec_levK_fp (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) :
    LocallyOfFinitePresentation (levBC φ E.f KK.levK ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) :=
  haveI := KK.levK_finitePresentation; inferInstance

theorem fec_levK_rank (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) (s' : ↥(Spec (CommRingCat.of S'))) :
    (levBC φ E.f KK.levK ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))).finrank s' = ℓ ^ 2 :=
  haveI := KK.levK_finite; haveI := KK.levK_flat; finrank_levBC φ E.f KK.levK ℓ KK.levK_rank s'

noncomputable def levKPtToBase (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) (k : Type u) [Field k] (sk' : S' →+* k)
    (P : {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) // FactorsThrough (levBC φ E.f KK.levK) P}) :
    {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough KK.levK P} :=
  ⟨rebase E.f (geomPoint_comp φ k sk') (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P.1),
    (factorsThrough_rebase KK.levK (geomPoint_comp φ k sk') _).mpr ((factorsThrough_iff φ E.f KK.levK _ P.1).mp P.2)⟩

noncomputable def levKPtOfBase (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) (k : Type u) [Field k] (sk' : S' →+* k)
    (Q : {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough KK.levK P}) :
    {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) // FactorsThrough (levBC φ E.f KK.levK) P} :=
  ⟨baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm Q.1), by
    rw [factorsThrough_iff, baseChangePointToBase_ofBase, factorsThrough_rebase]; exact Q.2⟩

theorem levKPtOfBase_toBase (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) (k : Type u) [Field k] (sk' : S' →+* k)
    (P : {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) // FactorsThrough (levBC φ E.f KK.levK) P}) :
    levKPtOfBase φ E KK k sk' (levKPtToBase φ E KK k sk' P) = P := by
  apply Subtype.ext
  show baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm
    (rebase E.f (geomPoint_comp φ k sk') (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P.1))) = P.1
  rw [rebase_symm_rebase, baseChangePointOfBase_toBase]

theorem levKPtToBase_ofBase (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) (k : Type u) [Field k] (sk' : S' →+* k)
    (Q : {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough KK.levK P}) :
    levKPtToBase φ E KK k sk' (levKPtOfBase φ E KK k sk' Q) = Q := by
  apply Subtype.ext
  show rebase E.f (geomPoint_comp φ k sk') (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ))
    (baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm Q.1))) = Q.1
  rw [baseChangePointToBase_ofBase, rebase_rebase_symm]

noncomputable def levKPtEquiv (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) (k : Type u) [Field k] (sk' : S' →+* k) :
    {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) // FactorsThrough (levBC φ E.f KK.levK) P} ≃
    {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough KK.levK P} :=
  ⟨levKPtToBase φ E KK k sk', levKPtOfBase φ E KK k sk', levKPtOfBase_toBase φ E KK k sk', levKPtToBase_ofBase φ E KK k sk'⟩

theorem levKPtOfBase_mul (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) (k : Type u) [Field k] (sk' : S' →+* k)
    (Q R : {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough KK.levK P})
    (QR : {P : SchemeHomOver (geomPoint k (sk'.comp φ)) E.f // FactorsThrough KK.levK P})
    (h : QR.1 = E.L.mul (geomPoint k (sk'.comp φ)) Q.1 R.1) :
    (levKPtOfBase φ E KK k sk' QR).1 =
      (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul (geomPoint k sk') (levKPtOfBase φ E KK k sk' Q).1 (levKPtOfBase φ E KK k sk' R).1 := by
  show baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm QR.1) =
    (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul (geomPoint k sk')
      (baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm Q.1))
      (baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (geomPoint_comp φ k sk').symm R.1))
  rw [baseChange_mul, baseChangePointToBase_ofBase, baseChangePointToBase_ofBase, ← rebase_mul, ← h]

theorem fec_levK_fibre (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) (k : Type u) [Field k] [IsAlgClosed k] (sk' : S' →+* k)
    (hN : (ℓ : k) ≠ 0) :
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) //
        FactorsThrough (levBC φ E.f KK.levK) P},
      ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk') (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) =
        (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul (geomPoint k sk') (e x) (e y) := by
  obtain ⟨e₀, he₀⟩ := KK.levK_fibre k (sk'.comp φ) hN
  exact ⟨e₀.trans (levKPtEquiv φ E KK k sk').symm, fun x y =>
    levKPtOfBase_mul φ E KK k sk' (e₀ x) (e₀ y) (e₀ (x + y)) (he₀ x y)⟩

theorem fec_levK_disjoint (E : FakeEllipticCurve Λ N S) (KK : E.ExtraLevel ℓ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (P : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    FactorsThrough (levBC φ E.f KK.levK) P → FactorsThrough (levBC φ E.f E.lev) P →
      P = (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).one t' := by
  intro hK hC
  rw [factorsThrough_iff] at hK hC
  apply (baseChangePointEquiv (Spec.map (CommRingCat.ofHom φ)) t').injective
  show baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _ = baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _
  rw [baseChangePointToBase_one]
  exact KK.levK_disjoint _ _ hK hC

end LevelK

section Trace

open scoped Quaternion
variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

noncomputable def tanToBase (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k)
    (P : SchemeHomOver (tangentBase k sk) (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) : SchemeHomOver (tangentBase k (sk.comp φ)) E.f :=
  rebase E.f (tangentBase_comp φ k sk) (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P)

theorem tanToBase_coe (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k)
    (P : SchemeHomOver (tangentBase k sk) (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    (tanToBase φ E k sk P).1 = P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom φ)) := rfl

theorem tanToBase_injective (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k) :
    Function.Injective (tanToBase φ E k sk) := fun P Q h => by
  apply (baseChangePointEquiv (Spec.map (CommRingCat.ofHom φ)) (tangentBase k sk)).injective
  apply Subtype.ext
  show (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) P).1 = (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) Q).1
  exact (tanToBase_coe φ E k sk P).symm.trans ((congrArg Subtype.val h).trans (tanToBase_coe φ E k sk Q))

theorem tanToBase_mul (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k)
    (P Q : SchemeHomOver (tangentBase k sk) (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    tanToBase φ E k sk ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul (tangentBase k sk) P Q) =
      E.L.mul (tangentBase k (sk.comp φ)) (tanToBase φ E k sk P) (tanToBase φ E k sk Q) := by
  show rebase E.f (tangentBase_comp φ k sk) (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ)) _) = _
  rw [baseChangePointToBase_mul, rebase_mul]; rfl

noncomputable def tanOfBase (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k)
    (P : SchemeHomOver (tangentBase k (sk.comp φ)) E.f) : SchemeHomOver (tangentBase k sk) (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) :=
  baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (tangentBase_comp φ k sk).symm P)

theorem tanToBase_ofBase (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k)
    (P : SchemeHomOver (tangentBase k (sk.comp φ)) E.f) : tanToBase φ E k sk (tanOfBase φ E k sk P) = P := by
  show rebase E.f (tangentBase_comp φ k sk) (baseChangePointToBase (Spec.map (CommRingCat.ofHom φ))
    (baseChangePointOfBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (tangentBase_comp φ k sk).symm P))) = P
  rw [baseChangePointToBase_ofBase, rebase_rebase_symm]

theorem tanOfBase_coe_fst (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k)
    (P : SchemeHomOver (tangentBase k (sk.comp φ)) E.f) :
    (tanOfBase φ E k sk P).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom φ)) = P.1 := by
  have h := congrArg Subtype.val (baseChangePointToBase_ofBase (Spec.map (CommRingCat.ofHom φ)) (rebase E.f (tangentBase_comp φ k sk).symm P))
  rw [baseChangePointToBase_coe, rebase_coe] at h
  exact h

theorem baseChange_one_coe_fst (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k) :
    ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).one (geomPoint k sk)).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom φ)) = (E.L.one (geomPoint k (sk.comp φ))).1 := by
  have h1 := congrArg Subtype.val (baseChangePointToBase_one (Spec.map (CommRingCat.ofHom φ)) E.L (geomPoint k sk))
  rw [baseChangePointToBase_coe] at h1
  rw [h1]
  have h2 := congrArg Subtype.val (rebase_one E.f E.L (geomPoint_comp φ k sk))
  rw [rebase_coe] at h2
  exact h2

theorem isTangentVector_tanToBase (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k)
    (P : SchemeHomOver (tangentBase k sk) (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))))
    (hP : IsTangentVector (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))) k sk P) : IsTangentVector E.L k (sk.comp φ) (tanToBase φ E k sk P) := by
  show tangentZero k ≫ (P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom φ))) = (E.L.one (geomPoint k (sk.comp φ))).1
  rw [← Category.assoc, show tangentZero k ≫ P.1 = _ from hP, baseChange_one_coe_fst]

theorem isTangentVector_tanOfBase (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S' →+* k)
    (P : SchemeHomOver (tangentBase k (sk.comp φ)) E.f) (hP : IsTangentVector E.L k (sk.comp φ) P) :
    IsTangentVector (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))) k sk (tanOfBase φ E k sk P) := by
  show tangentZero k ≫ (tanOfBase φ E k sk P).1 = ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).one (geomPoint k sk)).1
  apply pullback.hom_ext
  · rw [Category.assoc, baseChange_one_coe_fst, tanOfBase_coe_fst]
    exact hP
  · rw [Category.assoc, (tanOfBase φ E k sk P).2, ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).one (geomPoint k sk)).2,
      tangentZero_tangentBase]

theorem fec_act_trace (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] [IsAlgClosed k] (sk : S' →+* k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (τ : V → SchemeHomOver (tangentBase k sk) (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ)))) :
    Function.Injective τ →
    (∀ P : SchemeHomOver (tangentBase k sk) (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))),
      P ∈ Set.range τ ↔ IsTangentVector (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))) k sk P) →
    (∀ v w : V, τ (v + w) = (E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul (tangentBase k sk) (τ v) (τ w)) →
    (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
    ∀ (m : ↥Λ) (Φ : V →ₗ[k] V),
      (∀ v : V, τ (Φ v) = pushPt (act' φ (E.act m) (E.act_over m)) (act'_over φ _ _) (τ v)) →
    ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      LinearMap.trace k V Φ = (n : k) := by
  intro hinj hrange hadd hscale m Φ hΦ n hn
  refine E.act_trace k (sk.comp φ) V (fun v => tanToBase φ E k sk (τ v)) ?_ ?_ ?_ ?_ m Φ ?_ n hn
  · exact (tanToBase_injective φ E k sk).comp hinj
  · intro P
    constructor
    · rintro ⟨v, rfl⟩
      exact isTangentVector_tanToBase φ E k sk (τ v) ((hrange (τ v)).mp ⟨v, rfl⟩)
    · intro hP
      obtain ⟨v, hv⟩ := (hrange (tanOfBase φ E k sk P)).mpr (isTangentVector_tanOfBase φ E k sk P hP)
      exact ⟨v, by show tanToBase φ E k sk (τ v) = P; rw [hv, tanToBase_ofBase]⟩
  · intro v w
    show tanToBase φ E k sk (τ (v + w)) = E.L.mul _ (tanToBase φ E k sk (τ v)) (tanToBase φ E k sk (τ w))
    rw [hadd, tanToBase_mul]
  · intro c v
    show (tanToBase φ E k sk (τ (c • v))).1 = tangentScale k c ≫ (tanToBase φ E k sk (τ v)).1
    rw [tanToBase_coe, tanToBase_coe, hscale, Category.assoc]
  · intro v
    apply Subtype.ext
    show (tanToBase φ E k sk (τ (Φ v))).1 = (pushPt (E.act m) (E.act_over m) (tanToBase φ E k sk (τ v))).1
    rw [tanToBase_coe, hΦ, mapPt_coe, mapPt_coe, Category.assoc, act'_fst, tanToBase_coe, Category.assoc]

end Trace

end PullbackExists
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback.PullbackExists"

open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S', FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' := by
  classical
  obtain ⟨E, KK⟩ := u
  let ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom φ)
  haveI := E.bundle.smooth
  let E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S' :=
    { A := pullback E.f ι
      f := pullback.snd E.f ι
      L := E.L.baseChange ι
      comm := PullbackExists.fec_comm φ E
      bundle := PullbackExists.fec_bundle φ E
      dim_fibre := fun s' => by
        simpa using AlgebraicGeometry.topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
          φ E.f E.bundle.connectedFibres 2 E.dim_fibre s'
      act := fun x => PullbackExists.act' φ (E.act x) (E.act_over x)
      act_over := fun x => PullbackExists.act'_over φ _ _
      act_hom := fun x {T} t P Q => PullbackExists.fec_act_hom φ E x t P Q
      act_one := PullbackExists.fec_act_one φ E
      act_mul := PullbackExists.fec_act_mul φ E
      act_add := fun x y {T} t P => PullbackExists.fec_act_add φ E x y t P
      act_trace := PullbackExists.fec_act_trace φ E
      C := pullback (E.lev ≫ E.f) ι
      lev := PullbackExists.levBC φ E.f E.lev
      lev_closed := PullbackExists.fec_lev_closed φ E
      lev_sub := PullbackExists.fec_lev_sub φ E
      lev_one := PullbackExists.fec_lev_one φ E
      lev_torsion := PullbackExists.fec_lev_torsion φ E
      lev_stable := PullbackExists.fec_lev_stable φ E
      lev_finite := PullbackExists.fec_lev_finite φ E
      lev_flat := PullbackExists.fec_lev_flat φ E
      lev_finitePresentation := PullbackExists.fec_lev_fp φ E
      lev_rank := PullbackExists.fec_lev_rank φ E
      lev_fibre := PullbackExists.fec_lev_fibre φ E }
  let K' : E'.ExtraLevel ℓ :=
    { K := pullback (KK.levK ≫ E.f) ι
      levK := PullbackExists.levBC φ E.f KK.levK
      levK_closed := PullbackExists.fec_levK_closed φ E KK
      levK_sub := PullbackExists.fec_levK_sub φ E KK
      levK_one := PullbackExists.fec_levK_one φ E KK
      levK_torsion := PullbackExists.fec_levK_torsion φ E KK
      levK_stable := PullbackExists.fec_levK_stable φ E KK
      levK_disjoint := PullbackExists.fec_levK_disjoint φ E KK
      levK_finite := PullbackExists.fec_levK_finite φ E KK
      levK_flat := PullbackExists.fec_levK_flat φ E KK
      levK_finitePresentation := PullbackExists.fec_levK_fp φ E KK
      levK_rank := PullbackExists.fec_levK_rank φ E KK
      levK_fibre := PullbackExists.fec_levK_fibre φ E KK }
  refine ⟨⟨E', K'⟩, pullback.fst E.f ι, IsPullback.of_hasPullback E.f ι, ?_, ?_, ?_⟩
  · intro T t' P Q; exact PullbackExists.fec_mul_compat φ E t' P Q
  · intro x; exact PullbackExists.act'_fst φ (E.act x) (E.act_over x)
  · intro T t' P
    exact ⟨fun h => (PullbackExists.factorsThrough_iff φ E.f E.lev t' P).mp h,
      fun h => (PullbackExists.factorsThrough_iff φ E.f KK.levK t' P).mp h⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback (solution)
