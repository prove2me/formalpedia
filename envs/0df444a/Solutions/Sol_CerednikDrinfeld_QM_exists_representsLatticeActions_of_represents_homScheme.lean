-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_representsLatticeActions_of_represents_homScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d4f2a9f3-8577-5451-be1f-da2712e83d05

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_exists_tableScheme_of_represents_homScheme
import Theorems.Thm_CerednikDrinfeld_QM_LatticeAction_table_and_existsUnique_of_table
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_representsLatticeActions_of_represents_homScheme

set_option autoImplicit false

open scoped Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM"

universe u

namespace B1HAssembly

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

section Transport

variable {R R' : Type u} [CommRing R] [CommRing R'] {φ : R →+* R'}
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {L : RelativeGroupLaw R f}
  {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A}

theorem isPullback (hg : IsGroupPullback φ L L' g) : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)) :=
  hg.elim fun h _ => h

theorem mul_comp_g (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (P Q : SchemeHomOver t' f') :
    (L'.mul t' P Q).1 ≫ g =
      (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, (isPullback hg).w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, (isPullback hg).w, ← Category.assoc, Q.2]⟩).1 :=
  hg.elim fun _ h => h t' P Q

noncomputable def κ (hg : IsGroupPullback φ L L' g) : A' ≅ pullback f (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback hg).isoPullback

@[scoped simp] theorem κ_hom_fst (hg : IsGroupPullback φ L L' g) :
    (κ hg).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom φ)) = g :=
  (isPullback hg).isoPullback_hom_fst

@[scoped simp] theorem κ_hom_snd (hg : IsGroupPullback φ L L' g) :
    (κ hg).hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom φ)) = f' :=
  (isPullback hg).isoPullback_hom_snd

@[scoped simp] theorem κ_inv_g (hg : IsGroupPullback φ L L' g) :
    (κ hg).inv ≫ g = pullback.fst f (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback hg).isoPullback_inv_fst

@[scoped simp] theorem κ_inv_f' (hg : IsGroupPullback φ L L' g) :
    (κ hg).inv ≫ f' = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback hg).isoPullback_inv_snd

@[scoped simp] theorem κ_hom_fst_assoc (hg : IsGroupPullback φ L L' g) {Z : Scheme.{u}} (h : A ⟶ Z) :
    (κ hg).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ≫ h = g ≫ h := by
  rw [← Category.assoc, κ_hom_fst]

@[scoped simp] theorem κ_hom_snd_assoc (hg : IsGroupPullback φ L L' g) {Z : Scheme.{u}} (h : Spec (CommRingCat.of R') ⟶ Z) :
    (κ hg).hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ h = f' ≫ h := by
  rw [← Category.assoc, κ_hom_snd]

@[scoped simp] theorem κ_inv_g_assoc (hg : IsGroupPullback φ L L' g) {Z : Scheme.{u}} (h : A ⟶ Z) :
    (κ hg).inv ≫ g ≫ h = pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ≫ h := by
  rw [← Category.assoc, κ_inv_g]

@[scoped simp] theorem κ_inv_f'_assoc (hg : IsGroupPullback φ L L' g) {Z : Scheme.{u}} (h : Spec (CommRingCat.of R') ⟶ Z) :
    (κ hg).inv ≫ f' ≫ h = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ h := by
  rw [← Category.assoc, κ_inv_f']

def gPt (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (P : SchemeHomOver t' f') : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, (isPullback hg).w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem gPt_val (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (P : SchemeHomOver t' f') : (gPt hg t' P).1 = P.1 ≫ g := rfl

noncomputable def liftPt (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f) : SchemeHomOver t' f' :=
  ⟨pullback.lift Q.1 t' Q.2 ≫ (κ hg).inv, by rw [Category.assoc, κ_inv_f', pullback.lift_snd]⟩

@[scoped simp] theorem liftPt_val (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f) :
    (liftPt hg t' Q).1 = pullback.lift Q.1 t' Q.2 ≫ (κ hg).inv := rfl

theorem gPt_liftPt (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f) : gPt hg t' (liftPt hg t' Q) = Q :=
  Subtype.ext (by simp)

theorem gPt_injective (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    {P Q : SchemeHomOver t' f'} (h : gPt hg t' P = gPt hg t' Q) : P = Q :=
  Subtype.ext ((isPullback hg).hom_ext (congrArg Subtype.val h) (by rw [P.2, Q.2]))

theorem val_eq_of_comp_g_eq (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    {P Q : SchemeHomOver t' f'} (h : P.1 ≫ g = Q.1 ≫ g) : P = Q :=
  Subtype.ext ((isPullback hg).hom_ext h (by rw [P.2, Q.2]))

theorem liftPt_gPt (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (P : SchemeHomOver t' f') : liftPt hg t' (gPt hg t' P) = P :=
  gPt_injective hg t' (gPt_liftPt hg t' _)

theorem gPt_surjective (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f) : ∃ P, Q = gPt hg t' P :=
  ⟨liftPt hg t' Q, (gPt_liftPt hg t' Q).symm⟩

theorem lift_comp_κ_inv (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (P : SchemeHomOver t' f') (w : (P.1 ≫ g) ≫ f = t' ≫ Spec.map (CommRingCat.ofHom φ)) :
    pullback.lift (P.1 ≫ g) t' w ≫ (κ hg).inv = P.1 :=
  congrArg Subtype.val (liftPt_gPt hg t' P)

theorem gPt_mul (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (P Q : SchemeHomOver t' f') :
    gPt hg t' (L'.mul t' P Q) = L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (gPt hg t' P) (gPt hg t' Q) :=
  Subtype.ext (mul_comp_g hg t' P Q)

theorem isCommutative (hg : IsGroupPullback φ L L' g) (hc : L.IsCommutative) : L'.IsCommutative :=
  fun t' x y => gPt_injective hg t' (by rw [gPt_mul, gPt_mul]; exact hc _ _ _)

noncomputable def Ψ (hg : IsGroupPullback φ L L' g) (P : SchemeHomOver f' f') :
    SchemeHomOver (pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  gPt hg _ (GoodReductionJacobian.schemeHomOverComp (κ hg).inv (κ_inv_f' hg) P)

@[scoped simp] theorem Ψ_val (hg : IsGroupPullback φ L L' g) (P : SchemeHomOver f' f') :
    (Ψ hg P).1 = ((κ hg).inv ≫ P.1) ≫ g := rfl

theorem Ψ_mul (hg : IsGroupPullback φ L L' g) (P Q : SchemeHomOver f' f') :
    Ψ hg (L'.mul f' P Q) = L.mul _ (Ψ hg P) (Ψ hg Q) := by
  unfold Ψ
  rw [L'.mul_natural f' _ (κ hg).inv (κ_inv_f' hg), gPt_mul]

theorem Ψ_injective (hg : IsGroupPullback φ L L' g) {P Q : SchemeHomOver f' f'} (h : Ψ hg P = Ψ hg Q) : P = Q := by
  have h1 := gPt_injective hg _ h
  have h2 : (κ hg).inv ≫ P.1 = (κ hg).inv ≫ Q.1 := congrArg Subtype.val h1
  exact Subtype.ext ((cancel_epi (κ hg).inv).mp h2)

theorem lift_Ψ (hg : IsGroupPullback φ L L' g) (P : SchemeHomOver f' f')
    (w : (Ψ hg P).1 ≫ f = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ)) :
    pullback.lift (Ψ hg P).1 (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) w =
      (κ hg).inv ≫ P.1 ≫ (κ hg).hom := by
  apply pullback.hom_ext
  · simp
  · simp only [pullback.lift_snd, Category.assoc, κ_hom_snd]
    rw [P.2, κ_inv_f']

noncomputable def eOf (hg : IsGroupPullback φ L L' g) (χ : pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ A)
    (hχ : χ ≫ f = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ)) :
    SchemeHomOver f' f' :=
  ⟨(κ hg).hom ≫ pullback.lift χ _ hχ ≫ (κ hg).inv, by simp⟩

theorem Ψ_eOf (hg : IsGroupPullback φ L L' g) (χ : pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ A)
    (hχ : χ ≫ f = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ)) :
    Ψ hg (eOf hg χ hχ) = ⟨χ, hχ⟩ :=
  Subtype.ext (by simp [eOf])

end Transport

section Clauses

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def IsHomW (L : RelativeGroupLaw R f) (S' : Type u) [CommRing S']
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (χ : pullback f s ⟶ A) (hχ : χ ≫ f = pullback.snd f s ≫ s) : Prop :=
  ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
    pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ χ =
      (L.mul (t' ≫ s)
        ⟨pullback.lift P.1 t' P.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩
        ⟨pullback.lift Q.1 t' Q.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩).1

def TableW (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (S' : Type u) [CommRing S']
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ) (u : Fin (2 * 2) → ℤ)
    (φ : Fin (2 * 2) → (pullback f s ⟶ A)) (hφ : ∀ j, φ j ≫ f = pullback.snd f s ≫ s) : Prop :=
  letI := L.pointCommGroup hc (pullback.snd f s ≫ s)
  (∀ j k : Fin (2 * 2),
      (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (c j k l)) =
        ⟨pullback.lift (φ k) (pullback.snd f s) (hφ k) ≫ φ j, by rw [Category.assoc, hφ j, ← Category.assoc, pullback.lift_snd]⟩) ∧
    (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (u l)) = ⟨pullback.fst f s, pullback.condition⟩

theorem mul_congr_val (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {P P' Q Q' : SchemeHomOver t f} (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t P' Q').1 := by
  rw [Subtype.ext hP, Subtype.ext hQ]

end Clauses

section ClausesE

variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}

def IsHomE (L' : RelativeGroupLaw S' f') (e : A' ⟶ A') (he : e ≫ f' = f') : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t f'),
    pushPt e he (L'.mul t P Q) = L'.mul t (pushPt e he P) (pushPt e he Q)

def TableE (L' : RelativeGroupLaw S' f') (hc' : L'.IsCommutative)
    (c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ) (u : Fin (2 * 2) → ℤ)
    (e : Fin (2 * 2) → (A' ⟶ A')) (he : ∀ j, e j ≫ f' = f') : Prop :=
  letI := L'.pointCommGroup hc' f'
  (∀ j k : Fin (2 * 2), (∏ l, (⟨e l, he l⟩ : SchemeHomOver f' f') ^ (c j k l)) =
      ⟨e k ≫ e j, by rw [Category.assoc, he, he]⟩) ∧
    (∏ l, (⟨e l, he l⟩ : SchemeHomOver f' f') ^ (u l)) = ⟨𝟙 A', Category.id_comp _⟩

end ClausesE

section Transport2

variable {R R' : Type u} [CommRing R] [CommRing R'] {φ : R →+* R'}
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {L : RelativeGroupLaw R f}
  {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A}

@[scoped simp] theorem lift_comp_κ_inv_assoc (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' f')
    (w : (P.1 ≫ g) ≫ f = t' ≫ Spec.map (CommRingCat.ofHom φ)) {Z : Scheme.{u}} (h : A' ⟶ Z) :
    pullback.lift (P.1 ≫ g) t' w ≫ (κ hg).inv ≫ h = P.1 ≫ h := by
  rw [← Category.assoc, lift_comp_κ_inv]

theorem lift_mul_gPt (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (P Q : SchemeHomOver t f')
    (w : (L.mul (t ≫ Spec.map (CommRingCat.ofHom φ)) (gPt hg t P) (gPt hg t Q)).1 ≫ f =
      t ≫ Spec.map (CommRingCat.ofHom φ)) :
    pullback.lift (L.mul (t ≫ Spec.map (CommRingCat.ofHom φ)) (gPt hg t P) (gPt hg t Q)).1 t w ≫ (κ hg).inv =
      (L'.mul t P Q).1 := by
  rw [← cancel_mono (κ hg).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, κ_hom_fst]
    exact (mul_comp_g hg t P Q).symm
  · rw [pullback.lift_snd, Category.assoc, κ_hom_snd, (L'.mul t P Q).2]

@[scoped simp] theorem lift_mul_gPt_assoc (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (P Q : SchemeHomOver t f')
    (w : (L.mul (t ≫ Spec.map (CommRingCat.ofHom φ)) (gPt hg t P) (gPt hg t Q)).1 ≫ f =
      t ≫ Spec.map (CommRingCat.ofHom φ)) {Z : Scheme.{u}} (h : A' ⟶ Z) :
    pullback.lift (L.mul (t ≫ Spec.map (CommRingCat.ofHom φ)) (gPt hg t P) (gPt hg t Q)).1 t w ≫ (κ hg).inv ≫ h =
      (L'.mul t P Q).1 ≫ h := by
  rw [← Category.assoc, lift_mul_gPt]

theorem isHomW_iff (hg : IsGroupPullback φ L L' g) (e : SchemeHomOver f' f')
    (χ : pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ A)
    (hχ : χ ≫ f = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ))
    (hΨ : (Ψ hg e).1 = χ) :
    IsHomW L R' (Spec.map (CommRingCat.ofHom φ)) χ hχ ↔ IsHomE L' e.1 e.2 := by
  subst hΨ
  constructor
  · intro H T t P' Q'
    apply val_eq_of_comp_g_eq hg
    have H1 := H T t (gPt hg t P') (gPt hg t Q')
    simp only [Ψ_val, gPt_val, Category.assoc, lift_comp_κ_inv_assoc, lift_mul_gPt_assoc] at H1
    rw [mapPt_coe, Category.assoc, H1, mul_comp_g hg]
    exact mul_congr_val L _ (by simp) (by simp)
  · intro H T t P Q
    obtain ⟨P', rfl⟩ := gPt_surjective hg t P
    obtain ⟨Q', rfl⟩ := gPt_surjective hg t Q
    simp only [Ψ_val, gPt_val, Category.assoc, lift_comp_κ_inv_assoc, lift_mul_gPt_assoc]
    have H1 := congrArg (fun Z : SchemeHomOver t f' => Z.1 ≫ g) (H t P' Q')
    simp only [mapPt_coe, Category.assoc] at H1
    rw [H1, mul_comp_g hg]
    exact mul_congr_val L _ (by simp) (by simp)

theorem lift_eq_of_Ψ (hg : IsGroupPullback φ L L' g) (P : SchemeHomOver f' f')
    (χ : pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ A)
    (hχ : χ ≫ f = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ))
    (hΨ : (Ψ hg P).1 = χ) :
    pullback.lift χ (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) hχ = (κ hg).inv ≫ P.1 ≫ (κ hg).hom := by
  subst hΨ; exact lift_Ψ hg P hχ

theorem tableW_of_tableE (hg : IsGroupPullback φ L L' g) (hc : L.IsCommutative)
    (c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ) (u : Fin (2 * 2) → ℤ)
    (e : Fin (2 * 2) → SchemeHomOver f' f')
    (H : TableE L' (isCommutative hg hc) c u (fun l => (e l).1) (fun l => (e l).2)) :
    TableW L hc R' (Spec.map (CommRingCat.ofHom φ)) c u (fun l => (Ψ hg (e l)).1) (fun l => (Ψ hg (e l)).2) := by
  letI iE : CommGroup (SchemeHomOver f' f') := L'.pointCommGroup (isCommutative hg hc) f'
  letI iW : CommGroup (SchemeHomOver (pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ)) f) :=
    L.pointCommGroup hc _
  let ΨH : SchemeHomOver f' f' →* SchemeHomOver (pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ)) f :=
    MonoidHom.mk' (Ψ hg) (fun P Q => Ψ_mul hg P Q)
  have hΨH : ∀ P, ΨH P = Ψ hg P := fun _ => rfl
  obtain ⟨Hc, Hu⟩ := H
  refine ⟨fun j k => ?_, ?_⟩
  · have h1 := congrArg ΨH (Hc j k)
    rw [map_prod] at h1
    simp only [map_zpow] at h1
    simp only [hΨH] at h1
    beta_reduce
    refine h1.trans (Subtype.ext ?_)
    dsimp only
    rw [lift_Ψ hg (e k)]
    simp
  · have h1 := congrArg ΨH Hu
    rw [map_prod] at h1
    simp only [map_zpow] at h1
    simp only [hΨH] at h1
    beta_reduce
    refine h1.trans (Subtype.ext ?_)
    simp

theorem tableE_of_tableW (hg : IsGroupPullback φ L L' g) (hc : L.IsCommutative)
    (c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ) (u : Fin (2 * 2) → ℤ)
    (e : Fin (2 * 2) → SchemeHomOver f' f')
    (χ : Fin (2 * 2) → (pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ A))
    (hχ : ∀ j, χ j ≫ f = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ))
    (hΨ : ∀ j, Ψ hg (e j) = ⟨χ j, hχ j⟩)
    (H : TableW L hc R' (Spec.map (CommRingCat.ofHom φ)) c u χ hχ) :
    TableE L' (isCommutative hg hc) c u (fun l => (e l).1) (fun l => (e l).2) := by
  letI iE : CommGroup (SchemeHomOver f' f') := L'.pointCommGroup (isCommutative hg hc) f'
  letI iW : CommGroup (SchemeHomOver (pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ)) f) :=
    L.pointCommGroup hc _
  let ΨH : SchemeHomOver f' f' →* SchemeHomOver (pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ)) f :=
    MonoidHom.mk' (Ψ hg) (fun P Q => Ψ_mul hg P Q)
  have hinj : Function.Injective ΨH := fun P Q h => Ψ_injective hg h
  have hΨ' : ∀ l, ΨH ⟨(e l).1, (e l).2⟩ = ⟨χ l, hχ l⟩ := hΨ
  have hΨv : ∀ l, (Ψ hg (e l)).1 = χ l := fun l => congrArg Subtype.val (hΨ l)
  obtain ⟨Hc, Hu⟩ := H
  refine ⟨fun j k => hinj ?_, hinj ?_⟩
  · rw [map_prod]
    simp only [map_zpow, hΨ']
    refine (Hc j k).trans (Subtype.ext ?_)
    show pullback.lift (χ k) _ (hχ k) ≫ χ j = (Ψ hg ⟨(e k).1 ≫ (e j).1, _⟩).1
    rw [lift_eq_of_Ψ hg (e k) (χ k) (hχ k) (hΨv k), ← hΨv j]
    simp
  · rw [map_prod]
    simp only [map_zpow, hΨ']
    refine Hu.trans (Subtype.ext ?_)
    show pullback.fst f _ = (Ψ hg ⟨𝟙 A', _⟩).1
    simp

end Transport2

section Model

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (β : Fin (2 * 2) → ↥Λ)
variable {R R' : Type u} [CommRing R] [CommRing R'] {φ : R →+* R'}
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {L : RelativeGroupLaw R f}
  {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A}

def actPt (X' : LatticeAction Λ f' L') (j : Fin (2 * 2)) : SchemeHomOver f' f' :=
  ⟨X'.act (β j), X'.act_over (β j)⟩

@[scoped simp] theorem actPt_val (X' : LatticeAction Λ f' L') (j : Fin (2 * 2)) : (actPt β X' j).1 = X'.act (β j) := rfl

noncomputable def tup (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L') (j : Fin (2 * 2)) :
    pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶ A :=
  (Ψ hg (actPt β X' j)).1

theorem tup_def (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L') (j : Fin (2 * 2)) :
    tup β hg X' j = ((κ hg).inv ≫ X'.act (β j)) ≫ g := rfl

theorem tup_over (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L') (j : Fin (2 * 2)) :
    tup β hg X' j ≫ f = pullback.snd f (Spec.map (CommRingCat.ofHom φ)) ≫ Spec.map (CommRingCat.ofHom φ) :=
  (Ψ hg (actPt β X' j)).2

theorem tup_hom (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L') (j : Fin (2 * 2)) :
    IsHomW L R' (Spec.map (CommRingCat.ofHom φ)) (tup β hg X' j) (tup_over β hg X' j) :=
  (isHomW_iff hg (actPt β X' j) _ _ rfl).mpr (X'.act_hom (β j))

theorem tup_table (hg : IsGroupPullback φ L L' g) (hc : L.IsCommutative) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ)
    (hcH : ∀ j k : Fin (2 * 2), (β j : ℍ[ℚ, a, b]) * (β k : ℍ[ℚ, a, b]) = ∑ l, c j k l • (β l : ℍ[ℚ, a, b]))
    (u : Fin (2 * 2) → ℤ) (huH : (1 : ℍ[ℚ, a, b]) = ∑ l, u l • (β l : ℍ[ℚ, a, b]))
    (X' : LatticeAction Λ f' L') :
    TableW L hc R' (Spec.map (CommRingCat.ofHom φ)) c u (tup β hg X') (tup_over β hg X') :=
  tableW_of_tableE hg hc c u (actPt β X')
    ((CerednikDrinfeld.QM.LatticeAction.table_and_existsUnique_of_table Λ hΛ β hβ c hcH u huH f' L'
      (isCommutative hg hc)).1 X')

theorem baseChange_tup (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L')
    {R'' : Type u} [CommRing R''] (ψ : R' →+* R'') {A'' : Scheme.{u}} {f'' : A'' ⟶ Spec (CommRingCat.of R'')}
    {L'' : RelativeGroupLaw R'' f''} {g'' : A'' ⟶ A} (hg'' : IsGroupPullback (ψ.comp φ) L L'' g'')
    (X'' : LatticeAction Λ f'' L'') (h : A'' ⟶ A') (hh : IsGroupPullback ψ L' L'' h) (hhg : h ≫ g = g'')
    (hX : ∀ x : ↥Λ, X''.act x ≫ h = h ≫ X'.act x)
    (w : pullback.fst f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) ≫ f =
      (pullback.snd f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) ≫ Spec.map (CommRingCat.ofHom ψ)) ≫
        Spec.map (CommRingCat.ofHom φ)) (j : Fin (2 * 2)) :
    pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (ψ.comp φ))))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) ≫ Spec.map (CommRingCat.ofHom ψ)) w ≫ tup β hg X' j =
      tup β hg'' X'' j := by
  have key : pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (ψ.comp φ))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (ψ.comp φ))) ≫ Spec.map (CommRingCat.ofHom ψ)) w ≫ (κ hg).inv =
      (κ hg'').inv ≫ h := by
    rw [← cancel_mono (κ hg).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, Category.assoc, κ_hom_fst, hhg, κ_inv_g]
    · rw [pullback.lift_snd, Category.assoc, Category.assoc, κ_hom_snd, (isPullback hh).w, ← Category.assoc, κ_inv_f']
  rw [tup_def, tup_def, ← Category.assoc, ← Category.assoc, key]
  simp only [Category.assoc]
  rw [show h ≫ X'.act (β j) ≫ g = X''.act (β j) ≫ g'' by rw [← Category.assoc, ← hX, Category.assoc, hhg]]

theorem geomFibreH0Finrank_model_eq (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L') (𝓛 : A.Modules)
    (j : Fin (2 * 2)) (k : Type u) [Field k] (sk : R' →+* k) :
    Scheme.Modules.geomFibreH0Finrank f'
        ((Scheme.Modules.pullback g).obj 𝓛 ⊗
          (Scheme.Modules.pullback (X'.act (β j))).obj ((Scheme.Modules.pullback g).obj 𝓛)) k sk =
      Scheme.Modules.geomFibreH0Finrank (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj 𝓛 ⊗
          (Scheme.Modules.pullback (tup β hg X' j)).obj 𝓛) k sk := by
  have hpb : IsPullback (κ hg).hom f' (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom (RingHom.id R'))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hcomp : (κ hg).hom ≫ tup β hg X' j = X'.act (β j) ≫ g := by simp [tup_def]
  let e₁ : (Scheme.Modules.pullback (κ hg).hom).obj
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj 𝓛) ≅
      (Scheme.Modules.pullback g).obj 𝓛 :=
    (Scheme.Modules.pullbackComp (κ hg).hom (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr (κ_hom_fst hg)).app 𝓛
  let e₂ : (Scheme.Modules.pullback (κ hg).hom).obj ((Scheme.Modules.pullback (tup β hg X' j)).obj 𝓛) ≅
      (Scheme.Modules.pullback (X'.act (β j))).obj ((Scheme.Modules.pullback g).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (κ hg).hom (tup β hg X' j)).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app 𝓛 ≪≫
        ((Scheme.Modules.pullbackComp (X'.act (β j)) g).app 𝓛).symm
  let eIso := Scheme.Modules.pullbackTensorObjIso (κ hg).hom
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj 𝓛)
      ((Scheme.Modules.pullback (tup β hg X' j)).obj 𝓛) ≪≫ tensorIso e₁ e₂
  have := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback (RingHom.id R')
    (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) f' (κ hg).hom hpb _ _ eIso k sk
  simpa using this

end Model

section Generic

theorem range_subset_iInf_preimage_iff {E H T : Scheme.{u}} {ι : Type} [Fintype ι]
    (p : ι → (E ⟶ H)) (U : ι → H.Opens) (z : T ⟶ E) :
    Set.range z.base ⊆ ((⨅ j, (p j) ⁻¹ᵁ (U j) : E.Opens) : Set E) ↔
      ∀ j, Set.range (z ≫ p j).base ⊆ (U j : Set H) := by
  constructor
  · intro hz j
    rintro _ ⟨x, rfl⟩
    have hx : z.base x ∈ (⨅ j, (p j) ⁻¹ᵁ (U j) : E.Opens) := hz ⟨x, rfl⟩
    have hle : (⨅ j, (p j) ⁻¹ᵁ (U j) : E.Opens) ≤ (p j) ⁻¹ᵁ (U j) := iInf_le _ j
    have := hle hx
    simpa [Scheme.Hom.comp_base] using this
  · intro hz
    rintro _ ⟨x, rfl⟩
    have hmem : ∀ j, z.base x ∈ (p j) ⁻¹ᵁ (U j) := fun j => by
      have := hz j ⟨x, rfl⟩
      simpa [Scheme.Hom.comp_base] using this
    rw [← Finset.inf_univ_eq_iInf]
    show z.base x ∈ ((Finset.univ.inf fun j => (p j) ⁻¹ᵁ (U j) : E.Opens) : Set E)
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    simp only [Set.mem_iInter, Finset.mem_univ, Function.comp_apply]
    exact fun j _ => hmem j

end Generic

end B1HAssembly
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_representsLatticeActions_of_represents_homScheme.B1HAssembly"

open B1HAssembly

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (R : Type) [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 : A.Modules) (h𝓛₁ : Scheme.Modules.IsInvertible 𝓛) (h𝓛₂ : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : pullback f s ⟶ A), φ ≫ f = pullback.snd f s ≫ s → SchemeHomOver s πH)
    (hHnat : (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1))
    (hHsurj : (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) ∧
          pt S' s φ hφ = x))
    (hHinj : (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
          (φ φ' : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s) (hφ' : φ' ≫ f = pullback.snd f s ≫ s),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ'))
    (hHsep : IsSeparated πH) (hHlft : LocallyOfFiniteType πH) (hHlfp : LocallyOfFinitePresentation πH)
    (hHpieces : (∀ e : ℕ, ∃ U : H.Opens, IsClosed (U : Set H) ∧ QuasiCompact (U.ι ≫ πH) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
          (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
          (Set.range (pt S' s φ hφ).1.base ⊆ (U : Set H) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k),
              Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
                ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛 ⊗ (Scheme.Modules.pullback φ).obj 𝓛) k sk = e))) :
    ∃ (E : Scheme.{0}) (πE : E ⟶ Spec (CommRingCat.of R))
      (cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ A), IsGroupPullback φ L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE),
      RepresentsLatticeActions Λ L E πE cl ∧ IsSeparated πE ∧ LocallyOfFiniteType πE ∧ LocallyOfFinitePresentation πE ∧

      (∀ e : Fin (2 * 2) → ℕ, ∃ U : E.Opens, IsClosed (U : Set E) ∧ QuasiCompact (U.ι ≫ πE) ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
          (L' : RelativeGroupLaw R' f') (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L'),
          (Set.range (cl R' φ L' g hg X').1.base ⊆ (U : Set E) ↔
            ∀ (j : Fin (2 * 2)) (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k),
              Scheme.Modules.geomFibreH0Finrank f'
                ((Scheme.Modules.pullback g).obj 𝓛 ⊗
                  (Scheme.Modules.pullback (X'.act (β j))).obj ((Scheme.Modules.pullback g).obj 𝓛)) k sk = e j)) := by
  classical

  have hmem : ∀ jk : Fin (2 * 2) × Fin (2 * 2), (β jk.1 : ℍ[ℚ, a, b]) * (β jk.2 : ℍ[ℚ, a, b]) ∈ Λ :=
    fun jk => hΛ.mul_mem (β jk.1).2 (β jk.2).2
  choose c' hc' using fun jk : Fin (2 * 2) × Fin (2 * 2) => (hβ ⟨_, hmem jk⟩).exists
  obtain ⟨u, hu⟩ := (hβ ⟨1, hΛ.one_mem⟩).exists
  let c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ := fun j k => c' (j, k)
  have hcH : ∀ j k : Fin (2 * 2), (β j : ℍ[ℚ, a, b]) * (β k : ℍ[ℚ, a, b]) = ∑ l, c j k l • (β l : ℍ[ℚ, a, b]) := by
    intro j k
    have h := congrArg Subtype.val (hc' (j, k))
    simpa [Submodule.coe_sum] using h
  have huH : (1 : ℍ[ℚ, a, b]) = ∑ l, u l • (β l : ℍ[ℚ, a, b]) := by
    have h := congrArg Subtype.val hu
    simpa [Submodule.coe_sum] using h

  obtain ⟨E, πE, p, hp, hEsep, hElft, hElfp, hEpc, hTi, hTii⟩ :=
    AlgebraicGeometry.exists_tableScheme_of_represents_homScheme f L hc c u H πH pt hHnat hHsurj hHinj hHsep hHlft hHlfp

  have key : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L'),
      ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE,
        ∀ j, z.1 ≫ p j = (pt R' (Spec.map (CommRingCat.ofHom φ)) (tup β hg X' j) (tup_over β hg X' j)).1 :=
    fun R' _ φ _ _ L' g hg X' =>
      (hTii R' (Spec.map (CommRingCat.ofHom φ)) (tup β hg X') (tup_over β hg X') (tup_hom β hg X')).mpr
        (tup_table β hg hc hΛ hβ c hcH u huH X')
  choose cl hcl using key
  have ptcongr : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
      (χ χ' : pullback f s ⟶ A) (hχ : χ ≫ f = pullback.snd f s ≫ s) (hχ' : χ' ≫ f = pullback.snd f s ≫ s),
      χ = χ' → pt S' s χ hχ = pt S' s χ' hχ' := by
    rintro S' _ s χ χ' hχ hχ' rfl; rfl
  refine ⟨E, πE, cl, ⟨?_, ?_, ?_⟩, hEsep, hElft, hElfp, ?_⟩
  ·
    intro R' _ φ A' f' L' g hg X' R'' _ ψ A'' f'' L'' g'' hg'' X'' h hh hhg hX
    have hs : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    let z' : SchemeHomOver (Spec.map (CommRingCat.ofHom (ψ.comp φ))) πE :=
      ⟨Spec.map (CommRingCat.ofHom ψ) ≫ (cl R' φ L' g hg X').1, by rw [Category.assoc, (cl R' φ L' g hg X').2, hs]⟩
    suffices hzz : cl R'' (ψ.comp φ) L'' g'' hg'' X'' = z' from congrArg Subtype.val hzz
    apply hTi R'' _ _ z'
    intro j
    rw [hcl]
    show _ = (Spec.map (CommRingCat.ofHom ψ) ≫ (cl R' φ L' g hg X').1) ≫ p j
    rw [Category.assoc, hcl,
      ← hHnat R' R'' ψ (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (ψ.comp φ))) hs
        (tup β hg X' j) (tup_over β hg X' j)]
    exact congrArg Subtype.val (ptcongr R'' _ _ _ _ _ (baseChange_tup β hg X' ψ hg'' X'' h hh hhg hX _ j).symm)
  ·
    intro R' _ φ A' f' L' g hg spt
    have hx : ∀ j, (spt.1 ≫ p j) ≫ πH = Spec.map (CommRingCat.ofHom φ) := fun j => by
      rw [Category.assoc, hp, spt.2]
    choose χ hχ hW hptχ using fun j => hHsurj R' (Spec.map (CommRingCat.ofHom φ)) ⟨spt.1 ≫ p j, hx j⟩
    have tabW : TableW L hc R' (Spec.map (CommRingCat.ofHom φ)) c u χ hχ :=
      (hTii R' (Spec.map (CommRingCat.ofHom φ)) χ hχ hW).mp ⟨spt, fun j => by rw [hptχ]⟩
    let e : Fin (2 * 2) → SchemeHomOver f' f' := fun j => eOf hg (χ j) (hχ j)
    have hΨe : ∀ j, Ψ hg (e j) = ⟨χ j, hχ j⟩ := fun j => Ψ_eOf hg _ _
    have hhom : ∀ (j : Fin (2 * 2)) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t f'),
        pushPt (e j).1 (e j).2 (L'.mul t P Q) = L'.mul t (pushPt (e j).1 (e j).2 P) (pushPt (e j).1 (e j).2 Q) :=
      fun j => (isHomW_iff hg (e j) (χ j) (hχ j) (congrArg Subtype.val (hΨe j))).mp (hW j)
    have tabE : TableE L' (isCommutative hg hc) c u (fun j => (e j).1) (fun j => (e j).2) :=
      tableE_of_tableW hg hc c u e χ hχ hΨe tabW
    obtain ⟨X', hX'⟩ :=
      ((CerednikDrinfeld.QM.LatticeAction.table_and_existsUnique_of_table Λ hΛ β hβ c hcH u huH f' L'
        (isCommutative hg hc)).2 (fun j => (e j).1) (fun j => (e j).2) hhom tabE).exists
    refine ⟨X', hTi R' _ _ _ fun j => ?_⟩
    have htup : tup β hg X' j = χ j := by
      have h1 : actPt β X' j = e j := Subtype.ext (hX' j)
      rw [tup, h1, hΨe]
    rw [hcl, ptcongr R' _ _ _ _ (hχ j) htup, hptχ]
  ·
    intro R' _ φ A' f' L' g hg X₁ X₂ h12
    have htup : ∀ j, tup β hg X₁ j = tup β hg X₂ j := fun j => by
      apply hHinj R' (Spec.map (CommRingCat.ofHom φ)) _ _ (tup_over β hg X₁ j) (tup_over β hg X₂ j)
        (tup_hom β hg X₁ j) (tup_hom β hg X₂ j)
      apply Subtype.ext
      rw [← hcl R' φ L' g hg X₁ j, ← hcl R' φ L' g hg X₂ j, h12]
    have hact : ∀ j, X₁.act (β j) = X₂.act (β j) := fun j =>
      congrArg Subtype.val (Ψ_injective hg (P := actPt β X₁ j) (Q := actPt β X₂ j) (Subtype.ext (htup j)))
    obtain ⟨i, -, huniq⟩ :=
      (CerednikDrinfeld.QM.LatticeAction.table_and_existsUnique_of_table Λ hΛ β hβ c hcH u huH f' L'
        (isCommutative hg hc)).2 (fun j => X₁.act (β j)) (fun j => X₁.act_over (β j)) (fun j => X₁.act_hom (β j))
        ((CerednikDrinfeld.QM.LatticeAction.table_and_existsUnique_of_table Λ hΛ β hβ c hcH u huH f' L'
          (isCommutative hg hc)).1 X₁)
    exact (huniq X₁ fun j => rfl).trans (huniq X₂ fun j => (hact j).symm).symm
  ·
    intro e
    choose U hUc hUqc hUspec using fun j => hHpieces (e j)
    refine ⟨⨅ j, (p j) ⁻¹ᵁ (U j), (hEpc U hUc hUqc).1, (hEpc U hUc hUqc).2, ?_⟩
    intro R' _ φ A' f' L' g hg X'
    rw [range_subset_iInf_preimage_iff]
    refine forall_congr' fun j => ?_
    rw [hcl, hUspec j R' (Spec.map (CommRingCat.ofHom φ)) (tup β hg X' j) (tup_over β hg X' j) (tup_hom β hg X' j)]
    refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun sk => ?_
    rw [geomFibreH0Finrank_model_eq β hg X' 𝓛 j k sk]

end S_CerednikDrinfeld_QM_exists_representsLatticeActions_of_represents_homScheme
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_representsLatticeActions_of_represents_homScheme (solution)
