-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCanonicalPolData.pullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/8ef977c6-f7b2-5200-a549-ab718f49d7d9

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_of_isPullback

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

noncomputable section

namespace P2mKcCanonPolBCSol

theorem isPullback_of_lift {C : Type*} [Category C] {A A' B B' T T₁ : C} {f : A ⟶ B} {f' : A' ⟶ B'} {gA : A' ⟶ A}
    {b : B' ⟶ B} (hg : IsPullback gA f' f b) (ι'' : T ⟶ B') (ι₁ : T₁ ⟶ B) (j : T ⟶ T₁) (hbase : ι'' ≫ b = j ≫ ι₁)
    [HasPullback f' ι''] [HasPullback f ι₁]
    (u₁ : pullback f' ι'' ⟶ pullback f ι₁) (h1 : u₁ ≫ pullback.fst f ι₁ = pullback.fst f' ι'' ≫ gA)
    (h2 : u₁ ≫ pullback.snd f ι₁ = pullback.snd f' ι'' ≫ j) :
    IsPullback u₁ (pullback.snd f' ι'') (pullback.snd f ι₁) j := by
  have big := (IsPullback.of_hasPullback f' ι'').paste_horiz hg
  rw [← h1, hbase] at big
  exact IsPullback.of_right big h2 (IsPullback.of_hasPullback f ι₁)

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem mul_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain ⟨P, hP0⟩ := P; obtain ⟨Q, hQ0⟩ := Q; obtain ⟨P', hP1⟩ := P'; obtain ⟨Q', hQ1⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem inv_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of S)} (hs : s = s')
    (P : SchemeHomOver s f) (Q : SchemeHomOver s' f) (hPQ : P.1 = Q.1) : (L.inv s P).1 = (L.inv s' Q).1 := by
  subst hs; cases Subtype.ext hPQ; rfl

theorem locIsoOnBase_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

def transitionHom (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') :
    letI := G.pointGroup t; letI := G.pointGroup t''; SchemeHomOver t f →* SchemeHomOver t'' f :=
  letI := G.pointGroup t; letI := G.pointGroup t''
  { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
    map_one' := G.one_natural t t'' ψ hψ
    map_mul' := fun x y => G.mul_natural t t'' ψ hψ x y }

theorem inv_natural (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t'' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t; letI := G.pointGroup t''
  exact map_inv (transitionHom G t t'' ψ hψ) x

variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}

def pushAlong (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') : SchemeHomOver (t' ≫ ψ) f :=
  ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩

@[scoped simp] theorem pushAlong_val (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A)
    (hu : u ≫ f = f' ≫ ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    (pushAlong ψ u hu t' P).1 = P.1 ≫ u := rfl

section Hom

variable (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
  (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
  (hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ u =
      (L.mul (t' ≫ ψ)
        ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, Q.2]⟩).1)

def pushHom {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    letI := L'.pointGroup t'
    letI := L.pointGroup (t' ≫ ψ)
    SchemeHomOver t' f' →* SchemeHomOver (t' ≫ ψ) f :=
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  MonoidHom.mk' (fun P => pushAlong ψ u hu t' P) (fun P Q => Subtype.ext (hom T t' P Q))

include hom in
theorem pushAlong_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.mul t' P Q) = L.mul (t' ≫ ψ) (pushAlong ψ u hu t' P) (pushAlong ψ u hu t' Q) :=
  Subtype.ext (hom T t' P Q)

include hom in
theorem pushAlong_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    pushAlong ψ u hu t' (L'.one t') = L.one (t' ≫ ψ) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_one (pushHom L L' ψ u hu hom t')

include hom in
theorem pushAlong_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.inv t' P) = L.inv (t' ≫ ψ) (pushAlong ψ u hu t' P) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_inv (pushHom L L' ψ u hu hom t') P

include hom in

theorem one_val_comp {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    (L'.one t').1 ≫ u = (L.one (t' ≫ ψ)).1 :=
  congrArg Subtype.val (pushAlong_one L L' ψ u hu hom t')

include hom in

theorem negMor_comp : negMor f' L' ≫ u = u ≫ negMor f L := by
  have h1 : negMor f' L' ≫ u = (L.inv _ (pushAlong ψ u hu f' (idPt f'))).1 := by
    change (pushAlong ψ u hu f' (L'.inv f' (idPt f'))).1 = _
    rw [pushAlong_inv L L' ψ u hu hom]
  have h2 : u ≫ negMor f L = (L.inv (u ≫ f) (GoodReductionJacobian.schemeHomOverComp u rfl (idPt f))).1 := by
    change (GoodReductionJacobian.schemeHomOverComp u rfl (L.inv f (idPt f))).1 = _
    rw [inv_natural]
  rw [h1, h2]
  exact inv_val_congr L hu.symm _ _ (by simp [idPt])

include hom in

theorem addMor_comp :
    addMor f' L' ≫ u = pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ addMor f L := by
  have lhs := hom _ (pullback.fst f' f' ≫ f') ⟨pullback.fst f' f', rfl⟩ ⟨pullback.snd f' f', pullback.condition.symm⟩
  have rhs := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ pullback.fst f f ≫ f)
      (pullback.map f' f' f f u u ψ hu.symm hu.symm) rfl ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at rhs
  rw [addMor, addMor, lhs, rhs]
  refine mul_val_congr L ?_ _ _ _ _ ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst_assoc, hu]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_fst]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_snd]

include hom in
theorem nonempty_mumfordBundleIso (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) :
    Nonempty (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.map f' f' f f u u ψ hu.symm hu.symm)).obj (mumfordBundle f L 𝓛)) := by
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
  have hadd : addMor f' L' ≫ u = pp ≫ addMor f L := addMor_comp L L' ψ u hu hom
  have hfst : pullback.fst f' f' ≫ u = pp ≫ pullback.fst f f := by simp only [pp, pullback.lift_fst]
  have hsnd : pullback.snd f' f' ≫ u = pp ≫ pullback.snd f f := by simp only [pp, pullback.lift_snd]
  obtain ⟨D⟩ := hinv.pullback_dual_monoidalV2 u
  let J1 : (Scheme.Modules.pullback (addMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (addMor f' L') u).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hadd).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp pp (addMor f L)).app 𝓛).symm
  let J2 : (Scheme.Modules.pullback (pullback.fst f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.fst f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.fst f f)).app _).symm
  let J3 : (Scheme.Modules.pullback (pullback.snd f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.snd f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hsnd).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.snd f f)).app _).symm
  exact ⟨(J1 ⊗ᵢ (J2 ⊗ᵢ J3)) ≪≫
    whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso pp _ _).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso pp _ _).symm⟩

include hom in

theorem locIso_sliceAt_iff (hP : IsPullback u f' f ψ) (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛)
    {R : Type u} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) (x' : SchemeHomOver t' f') :
    LocIsoOnBase (pullback.snd f' t')
        ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)))
        (𝟙_ ((pullback f' t').Modules)) ↔
      LocIsoOnBase (pullback.snd f (t' ≫ ψ))
        ((Scheme.Modules.pullback (sliceAt f (pushAlong ψ u hu t' x'))).obj (mumfordBundle f L 𝓛))
        (𝟙_ ((pullback f (t' ≫ ψ)).Modules)) := by
  obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L L' ψ u hu hom 𝓛 hinv
  let x : SchemeHomOver (t' ≫ ψ) f := pushAlong ψ u hu t' x'
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm

  let r : pullback f (t' ≫ ψ) ⟶ pullback f' t' :=
    pullback.lift
      (hP.lift (pullback.fst f (t' ≫ ψ)) (pullback.snd f (t' ≫ ψ) ≫ t')
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.snd f (t' ≫ ψ)) (by rw [IsPullback.lift_snd])
  let s : pullback f' t' ⟶ pullback f (t' ≫ ψ) :=
    pullback.lift (pullback.fst f' t' ≫ u) (pullback.snd f' t')
      (by rw [Category.assoc, hu, ← Category.assoc, pullback.condition, Category.assoc])
  have hr : r ≫ pullback.snd f' t' = pullback.snd f (t' ≫ ψ) ≫ 𝟙 _ := by
    simp only [r, pullback.lift_snd, Category.comp_id]
  have hs : s ≫ pullback.snd f (t' ≫ ψ) = pullback.snd f' t' ≫ 𝟙 _ := by
    simp only [s, pullback.lift_snd, Category.comp_id]
  have hslice_r : (r ≫ sliceAt f' x') ≫ pp = sliceAt f x := by
    apply pullback.hom_ext
    · simp only [r, pp, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
    · simp only [r, pp, sliceAt, x, pushAlong, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  have hslice_s : s ≫ sliceAt f x = sliceAt f' x' ≫ pp := by
    apply pullback.hom_ext
    · simp only [s, pp, sliceAt, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [s, pp, sliceAt, x, pushAlong, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

  let I1r : (Scheme.Modules.pullback r).obj (𝟙_ (pullback f' t').Modules) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorUnitObjIso r
  let I2r : (Scheme.Modules.pullback r).obj
        ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛))) ≅
      (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) :=
    (Scheme.Modules.pullback r).mapIso ((Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso) ≪≫
      (Scheme.Modules.pullbackComp r (sliceAt f' x')).app _ ≪≫
        (Scheme.Modules.pullbackComp (r ≫ sliceAt f' x') pp).app _ ≪≫
          (Scheme.Modules.pullbackCongr hslice_r).app _

  let I1s : (Scheme.Modules.pullback s).obj (𝟙_ (pullback f (t' ≫ ψ)).Modules) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorUnitObjIso s
  let I2s : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) ≅
      (Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) :=
    (Scheme.Modules.pullbackComp s (sliceAt f x)).app _ ≪≫
      (Scheme.Modules.pullbackCongr hslice_s).app _ ≪≫
        ((Scheme.Modules.pullbackComp (sliceAt f' x') pp).app _).symm ≪≫
          (Scheme.Modules.pullback (sliceAt f' x')).mapIso ΛIso.symm
  constructor
  · intro H'
    have Hr := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
      (g := pullback.snd f' t') (pullback.snd f (t' ≫ ψ)) r (𝟙 _) hr H'
    exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I2r.symm)
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans Hr (locIsoOnBase_of_iso _ I1r))
  · intro H
    have Hs := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
      (g := pullback.snd f (t' ≫ ψ)) (pullback.snd f' t') s (𝟙 _) hs H
    exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ I2s.symm)
      ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans Hs (locIsoOnBase_of_iso _ I1s))

include hom in

theorem mul_self_eq_one_iff (hP : IsPullback u f' f ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
    (x' : SchemeHomOver t' f') :
    L'.mul t' x' x' = L'.one t' ↔
      L.mul (t' ≫ ψ) (pushAlong ψ u hu t' x') (pushAlong ψ u hu t' x') = L.one (t' ≫ ψ) := by
  constructor
  · intro h
    rw [← pushAlong_mul L L' ψ u hu hom, h, pushAlong_one L L' ψ u hu hom]
  · intro h
    apply Subtype.ext
    apply hP.hom_ext
    · rw [one_val_comp L L' ψ u hu hom t']
      exact (hom T t' x' x').trans (congrArg Subtype.val h)
    · rw [(L'.mul t' x' x').2, (L'.one t').2]

include hom in

theorem kernelTrivial_of_isPullback (hP : IsPullback u f' f ψ)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hker : KernelTrivial f L 𝓛) :
    KernelTrivial f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  intro R _ t' x' H'
  have hx : pushAlong ψ u hu t' x' = L.one (t' ≫ ψ) :=
    hker R (t' ≫ ψ) (pushAlong ψ u hu t' x') ((locIso_sliceAt_iff L L' ψ u hu hom hP 𝓛 hinv t' x').1 H')
  apply Subtype.ext
  apply hP.hom_ext
  · rw [one_val_comp L L' ψ u hu hom t']
    exact congrArg Subtype.val hx
  · rw [x'.2, (L'.one t').2]

include hom in

theorem kernelIsTwoTorsion_of_isPullback (hP : IsPullback u f' f ψ)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hK : KernelIsTwoTorsion f L 𝓛) :
    KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  intro R _ t' x'
  rw [locIso_sliceAt_iff L L' ψ u hu hom hP 𝓛 hinv t' x', hK R (t' ≫ ψ) (pushAlong ψ u hu t' x'),
    mul_self_eq_one_iff L L' ψ u hu hom hP t' x']

include hom in
theorem rosatiCompatible_of_comm {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ b : I, act b ≫ f = f)
    (act' : I → (A' ⟶ A')) (act'_over : ∀ b : I, act' b ≫ f' = f') (hact : ∀ b : I, act' b ≫ u = u ≫ act b)
    (star : I → I) (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛)
    (hros : RosatiCompatible f L 𝓛 act act_over star) :
    RosatiCompatible f' L' ((Scheme.Modules.pullback u).obj 𝓛) act' act'_over star := by
  obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L L' ψ u hu hom 𝓛 hinv
  intro b
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
  have comm : pp ≫ (pullback.fst f f ≫ f) = (pullback.fst f' f' ≫ f') ≫ ψ := by
    simp only [pp, Category.assoc, pullback.lift_fst_assoc, hu]
  have H := AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
    (g := pullback.fst f f ≫ f) (pullback.fst f' f' ≫ f') pp ψ comm (hros b)

  let m : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)
  let m' : pullback f' f' ⟶ pullback f' f' :=
    pullback.lift (pullback.fst f' f') (pullback.snd f' f' ≫ act' b)
      (by rw [Category.assoc, act'_over]; exact pullback.condition)
  let n : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f)
      (by rw [Category.assoc, act_over]; exact pullback.condition)
  let n' : pullback f' f' ⟶ pullback f' f' :=
    pullback.lift (pullback.fst f' f' ≫ act' (star b)) (pullback.snd f' f')
      (by rw [Category.assoc, act'_over]; exact pullback.condition)
  have hm : m' ≫ pp = pp ≫ m := by
    apply pullback.hom_ext
    · simp only [m, m', pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [m, m', pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hact]
  have hn : n' ≫ pp = pp ≫ n := by
    apply pullback.hom_ext
    · simp only [n, n', pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hact]
    · simp only [n, n', pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  let Im : (Scheme.Modules.pullback m').obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback m).obj (mumfordBundle f L 𝓛)) :=
    (Scheme.Modules.pullback m').mapIso ΛIso ≪≫ (Scheme.Modules.pullbackComp m' pp).app _ ≪≫
      (Scheme.Modules.pullbackCongr hm).app _ ≪≫ ((Scheme.Modules.pullbackComp pp m).app _).symm
  let In : (Scheme.Modules.pullback n').obj (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback n).obj (mumfordBundle f L 𝓛)) :=
    (Scheme.Modules.pullback n').mapIso ΛIso ≪≫ (Scheme.Modules.pullbackComp n' pp).app _ ≪≫
      (Scheme.Modules.pullbackCongr hn).app _ ≪≫ ((Scheme.Modules.pullbackComp pp n).app _).symm
  exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ Im)
    ((AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans H (locIsoOnBase_of_iso _ In.symm))

include hom in

theorem isSymmetric_of_comm (𝓛 : A.Modules) (hs : IsSymmetric f L 𝓛) :
    IsSymmetric f' L' ((Scheme.Modules.pullback u).obj 𝓛) := by
  have h1 : LocIsoOnBase f' ((Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛))
      ((Scheme.Modules.pullback u).obj 𝓛) :=
    AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (g := f) f' u ψ hu hs
  have e : (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (negMor f' L') u).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr (negMor_comp L L' ψ u hu hom)).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp u (negMor f L)).app 𝓛).symm
  exact (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence f').trans (locIsoOnBase_of_iso f' e) h1

include hom in

theorem root_transport (hP : IsPullback u f' f ψ) (M 𝓛₀ : A.Modules) (h0inv : Scheme.Modules.IsInvertible 𝓛₀)
    (h0ker : KernelTrivial f L 𝓛₀)
    (h0loc : LocIsoOnBase f M (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback u).obj 𝓛₀) ∧
      KernelTrivial f' L' ((Scheme.Modules.pullback u).obj 𝓛₀) ∧
      LocIsoOnBase f' ((Scheme.Modules.pullback u).obj M)
        ((Scheme.Modules.pullback u).obj 𝓛₀ ⊗
          (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛₀)) := by
  refine ⟨h0inv.pullback u, kernelTrivial_of_isPullback L L' ψ u hu hom hP 𝓛₀ h0inv h0ker, ?_⟩
  have H : LocIsoOnBase f' ((Scheme.Modules.pullback u).obj M)
      ((Scheme.Modules.pullback u).obj (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀)) :=
    AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (g := f) f' u ψ hu h0loc
  refine (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence f').trans H (locIsoOnBase_of_iso f' ?_)
  exact Scheme.Modules.pullbackTensorObjIso u _ _ ≪≫
    whiskerLeftIso _
      ((Scheme.Modules.pullbackComp u (negMor f L)).app 𝓛₀ ≪≫
        (Scheme.Modules.pullbackCongr (negMor_comp L L' ψ u hu hom).symm).app 𝓛₀ ≪≫
        ((Scheme.Modules.pullbackComp (negMor f' L') u).app 𝓛₀).symm)

end Hom

theorem pos_of_isPullback {φ : S →+* S'} {gA : A' ⟶ A} (hg : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    {𝓛 : A.Modules}
    (hpos : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S' →+* k) :
    0 < Scheme.Modules.geomFibreH0Finrank f' ((Scheme.Modules.pullback gA).obj 𝓛) k sk := by
  rw [← Scheme.Modules.geomFibreH0Finrank_comp_eq_of_isPullback_of_iso φ f f' gA hg 𝓛 _ ⟨Iso.refl _⟩ k sk]
  exact hpos k (sk.comp φ)

theorem root_clause_transport (φ : S →+* S')
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (gA : A' ⟶ A) (hg : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ gA =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules)
    (S₁ : Type u) [CommRing S₁] [Algebra S S₁] (S₂ : Type u) [CommRing S₂] [Algebra S' S₂] (κ : S₁ →+* S₂)
    (hκ : (algebraMap S' S₂).comp φ = κ.comp (algebraMap S S₁))
    (hroot : ∀ (L₁ : RelativeGroupLaw S₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₁))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))),
            (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))),
                  by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))),
                  by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧
          KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) L₁ 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback
              (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) L₁)).obj 𝓛₀))
    (L₂ : RelativeGroupLaw S₂ (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))))
    (hL₂ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₂))
        (P Q : SchemeHomOver t' (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))),
        (L₂.mul t' P Q).1 ≫ pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))) =
          (L'.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))
            ⟨P.1 ≫ pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    ∃ 𝓛₀ : (pullback f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))).Modules,
      Scheme.Modules.IsInvertible 𝓛₀ ∧
      KernelTrivial (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))) L₂ 𝓛₀ ∧
      LocIsoOnBase (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))
        ((Scheme.Modules.pullback (pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))).obj
          ((Scheme.Modules.pullback gA).obj 𝓛))
        (𝓛₀ ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))) L₂)).obj 𝓛₀) := by

  have hbase : Spec.map (CommRingCat.ofHom (algebraMap S' S₂)) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₁)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ]

  obtain ⟨u₁, hu₁1, hu₁2⟩ :
      ∃ u₁ : pullback f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))) ⟶
          pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))),
        u₁ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))) =
            pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))) ≫ gA ∧
          u₁ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))) =
            pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))) ≫ Spec.map (CommRingCat.ofHom κ) :=
    ⟨pullback.lift (pullback.fst f' _ ≫ gA) (pullback.snd f' _ ≫ Spec.map (CommRingCat.ofHom κ))
        (by rw [Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc, hbase, Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hP₁ : IsPullback u₁ (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) (Spec.map (CommRingCat.ofHom κ)) :=
    isPullback_of_lift hg _ _ _ hbase u₁ hu₁1 hu₁2

  have hL₁ := fun (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₁))
      (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))) =>
    congrArg Subtype.val
      (RelativeGroupLaw.baseChangePointToBase_mul (Spec.map (CommRingCat.ofHom (algebraMap S S₁))) L t' P Q)
  obtain ⟨𝓛₀, h0inv, h0ker, h0loc⟩ := hroot (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) hL₁

  have homU : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S₂))
      (P Q : SchemeHomOver t (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))),
      (L₂.mul t P Q).1 ≫ u₁ =
        ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))).mul (t ≫ Spec.map (CommRingCat.ofHom κ))
          ⟨P.1 ≫ u₁, by rw [Category.assoc, hu₁2, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ u₁, by rw [Category.assoc, hu₁2, ← Category.assoc, Q.2]⟩).1 := by
    intro T t P Q
    apply pullback.hom_ext
    · conv_lhs => rw [Category.assoc, hu₁1, ← Category.assoc, hL₂ T t P Q, hom]
      conv_rhs => rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
      refine mul_val_congr L ?_ _ _ _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, hbase]
      · simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hu₁1]
      · simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hu₁1]
    · conv_lhs => rw [Category.assoc, hu₁2, ← Category.assoc, (L₂.mul t P Q).2]
      exact (((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))).mul
        (t ≫ Spec.map (CommRingCat.ofHom κ)) _ _).2).symm
  obtain ⟨hI, hKer, hLoc⟩ := root_transport (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) L₂
    (Spec.map (CommRingCat.ofHom κ)) u₁ hu₁2 homU hP₁
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))).obj 𝓛)
    𝓛₀ h0inv h0ker h0loc
  refine ⟨(Scheme.Modules.pullback u₁).obj 𝓛₀, hI, hKer, ?_⟩
  refine (AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso _ ?_) hLoc
  exact (Scheme.Modules.pullbackComp (pullback.fst f' _) gA).app 𝓛 ≪≫
    (Scheme.Modules.pullbackCongr hu₁1.symm).app 𝓛 ≪≫
    ((Scheme.Modules.pullbackComp u₁ (pullback.fst f _)).app 𝓛).symm

end P2mKcCanonPolBCSol
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_of_isPullback.P2mKcCanonPolBCSol"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_of_isPullback.P2mKcCanonPolBCSol"

open P2mKcCanonPolBCSol in
theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act' : I → (A' ⟶ A')) (act_over' : ∀ x : I, act' x ≫ f' = f') (star : I → I)
    (gA : A' ⟶ A) (hg : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ gA =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hact : ∀ x : I, act' x ≫ gA = gA ≫ act x)
    (𝓛 : A.Modules) (h𝓛 : IsCanonicalPolData f L act act_over star 𝓛) :
    IsCanonicalPolData f' L' act' act_over' star ((Scheme.Modules.pullback gA).obj 𝓛) := by
  obtain ⟨hinv, hsymm, hK, ⟨S₁, _i1, _i2, hff, hroot⟩, hpos, hros⟩ := h𝓛
  have hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ gA =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1 :=
    fun T t' P Q => hmul t' P Q
  refine ⟨hinv.pullback gA, isSymmetric_of_comm L L' _ gA hg.w hom 𝓛 hsymm,
    kernelIsTwoTorsion_of_isPullback L L' _ gA hg.w hom hg 𝓛 hinv hK, ?_, pos_of_isPullback hg hpos,
    rosatiCompatible_of_comm L L' _ gA hg.w hom act act_over act' act_over' hact star 𝓛 hinv hros⟩

  letI : Algebra S S' := φ.toAlgebra
  haveI : Module.FaithfullyFlat S S₁ := hff
  have hκ : (algebraMap S' (S' ⊗[S] S₁)).comp φ =
      (Algebra.TensorProduct.includeRight : S₁ →ₐ[S] S' ⊗[S] S₁).toRingHom.comp (algebraMap S S₁) := by
    refine RingHom.ext fun s => ?_
    change algebraMap S' (S' ⊗[S] S₁) (algebraMap S S' s) = (1 : S') ⊗ₜ[S] algebraMap S S₁ s
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact ⟨S' ⊗[S] S₁, inferInstance, inferInstance, inferInstance,
    root_clause_transport φ L L' gA hg hom 𝓛 S₁ (S' ⊗[S] S₁) _ hκ hroot⟩

end S_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_of_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_of_isPullback (solution)
