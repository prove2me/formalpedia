-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCanonicalPolData.pullback_inv_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/51fe417a-a08d-59b1-8573-86adb11e5846

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pullback_inv_of_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_pullback_inv_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_inv_of_iso

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

namespace CaBody

variable {S : Type u} [CommRing S]

theorem schemeHomOverComp_inv {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI : Group (SchemeHomOver t f) := L.pointGroup t
  letI : Group (SchemeHomOver t' f) := L.pointGroup t'
  let Φ : SchemeHomOver t f →* SchemeHomOver t' f :=
    MonoidHom.mk' (fun x => schemeHomOverComp ψ hψ x) (fun x y => L.mul_natural t t' ψ hψ x y)
  exact map_inv Φ x

theorem comp_negMor {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f) :
    x.1 ≫ negMor f L = (L.inv t x).1 := by
  have h := schemeHomOverComp_inv L f t x.1 x.2 (idPt f)
  have h2 : schemeHomOverComp x.1 x.2 (idPt f) = x := by apply Subtype.ext; simp [schemeHomOverComp, idPt]
  rw [h2] at h
  have := congrArg Subtype.val h
  simpa [schemeHomOverComp, negMor] using this

theorem locIsoOnBase_of_iso {S' : Type u} [CommRing S'] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

end CaBody

open CaBody in
theorem solution
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f')
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act' : I → (A' ⟶ A')) (act_over' : ∀ x : I, act' x ≫ f' = f') (star : I → I)
    (e : A ≅ A') (he : e.hom ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f),
      (L.mul t x y).1 ≫ e.hom =
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)
    (hact : ∀ x : I, act x ≫ e.hom = e.hom ≫ act' x)
    (𝓛 : A.Modules) (h𝓛 : IsCanonicalPolData f L act act_over star 𝓛) :
    IsCanonicalPolData f' L' act' act_over' star ((Scheme.Modules.pullback e.inv).obj 𝓛) := by

  have hg : e.inv ≫ f = f' := by rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

  have hmul' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
      mapPt e.inv hg (L'.mul t P Q) = L.mul t (mapPt e.inv hg P) (mapPt e.inv hg Q) := by
    intro T t P Q
    have key := hmul t (mapPt e.inv hg P) (mapPt e.inv hg Q)

    have hP : (⟨(mapPt e.inv hg P).1 ≫ e.hom, by rw [Category.assoc, he]; exact (mapPt e.inv hg P).2⟩ : SchemeHomOver t f') = P := by
      apply Subtype.ext; simp [mapPt]
    have hQ : (⟨(mapPt e.inv hg Q).1 ≫ e.hom, by rw [Category.assoc, he]; exact (mapPt e.inv hg Q).2⟩ : SchemeHomOver t f') = Q := by
      apply Subtype.ext; simp [mapPt]
    rw [hP, hQ] at key
    apply Subtype.ext
    simp only [mapPt_coe]
    rw [← key, Category.assoc, e.hom_inv_id, Category.comp_id]

  have hneg : negMor f' L' ≫ e.inv = e.inv ≫ negMor f L := by
    letI : Group (SchemeHomOver f' f') := L'.pointGroup f'
    letI : Group (SchemeHomOver f' f) := L.pointGroup f'
    let Φ : SchemeHomOver f' f' →* SchemeHomOver f' f := MonoidHom.mk' (fun P => mapPt e.inv hg P) (fun P Q => hmul' f' P Q)
    have h1 : mapPt e.inv hg (L'.inv f' (idPt f')) = L.inv f' (mapPt e.inv hg (idPt f')) := map_inv Φ (idPt f')
    have h2 : (mapPt e.inv hg (idPt f') : SchemeHomOver f' f) = ⟨e.inv, hg⟩ := by apply Subtype.ext; simp [idPt]
    rw [h2] at h1
    have := congrArg Subtype.val h1
    rw [mapPt_coe] at this
    change (L'.inv f' (idPt f')).1 ≫ e.inv = e.inv ≫ negMor f L
    rw [this, ← comp_negMor L f' ⟨e.inv, hg⟩]

  have hact' : ∀ x : I, act' x ≫ e.inv = e.inv ≫ act x := by
    intro x
    have := hact x
    rw [← cancel_epi e.hom, ← Category.assoc, ← Category.assoc, e.hom_inv_id, Category.id_comp]
    rw [← cancel_mono e.hom]; simp only [Category.assoc, e.inv_hom_id, Category.comp_id]; exact this.symm
  obtain ⟨hinv, hsym, hK2, hroot, hpos, hros⟩ := h𝓛
  refine ⟨hinv.pullback e.inv, ?sym, ?k2, ?root, ?pos, ?ros⟩
  case sym =>

    have e1 : (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback e.inv).obj 𝓛) ≅
        (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) :=
      (Scheme.Modules.pullbackComp (negMor f' L') e.inv).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hneg).app 𝓛 ≪≫
        ((Scheme.Modules.pullbackComp e.inv (negMor f L)).app 𝓛).symm
    have key := LocIsoOnBase.pullback_of_comp_eq f' e.inv (𝟙 _) (by rw [Category.comp_id]; exact hg) hsym
    exact (LocIsoOnBase.equivalence f').trans (locIsoOnBase_of_iso _ e1) key
  case k2 => exact AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible L L' e he hmul 𝓛 hinv hK2
  case root => exact AlgebraicGeometry.Polarisation.exists_faithfullyFlat_kernelTrivial_locIsoOnBase_pullback_inv_of_iso L L' e he hmul 𝓛 hinv hroot
  case pos =>
    intro k _ _ sk
    rw [AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pullback_inv_of_iso f f' e he 𝓛 k sk]
    exact hpos k sk
  case ros =>
    intro b
    let GG : pullback f' f' ⟶ pullback f f :=
      pullback.lift (pullback.fst f' f' ≫ e.inv) (pullback.snd f' f' ≫ e.inv) (by simp only [Category.assoc, hg]; exact pullback.condition)
    have hGG1 : GG ≫ pullback.fst f f = pullback.fst f' f' ≫ e.inv := pullback.lift_fst _ _ _
    have hGG2 : GG ≫ pullback.snd f f = pullback.snd f' f' ≫ e.inv := pullback.lift_snd _ _ _
    have hGGt : GG ≫ (pullback.fst f f ≫ f) = pullback.fst f' f' ≫ f' := by
      rw [← Category.assoc, hGG1, Category.assoc, hg]

    have hmG : addMor f' L' ≫ e.inv = GG ≫ addMor f L := by
      let P₁' : SchemeHomOver (pullback.fst f' f' ≫ f') f' := ⟨pullback.fst f' f', rfl⟩
      let P₂' : SchemeHomOver (pullback.fst f' f' ≫ f') f' := ⟨pullback.snd f' f', pullback.condition.symm⟩
      let P₁ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.fst f f, rfl⟩
      let P₂ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.snd f f, pullback.condition.symm⟩
      have e₁ : schemeHomOverComp GG hGGt P₁ = mapPt e.inv hg P₁' := by
        apply Subtype.ext; show GG ≫ pullback.fst f f = _; rw [hGG1]; rfl
      have e₂ : schemeHomOverComp GG hGGt P₂ = mapPt e.inv hg P₂' := by
        apply Subtype.ext; show GG ≫ pullback.snd f f = _; rw [hGG2]; rfl
      have lhs : addMor f' L' ≫ e.inv = (L.mul _ (mapPt e.inv hg P₁') (mapPt e.inv hg P₂')).1 := by
        have := congrArg Subtype.val (hmul' (pullback.fst f' f' ≫ f') P₁' P₂')
        first | exact this | simpa [mapPt, addMor] using this
      have rhs : GG ≫ addMor f L = (L.mul _ (schemeHomOverComp GG hGGt P₁) (schemeHomOverComp GG hGGt P₂)).1 := by
        have := congrArg Subtype.val (L.mul_natural (pullback.fst f f ≫ f) (pullback.fst f' f' ≫ f') GG hGGt P₁ P₂)
        first | exact this | simpa [schemeHomOverComp, addMor] using this
      rw [lhs, rhs, e₁, e₂]
    obtain ⟨ed⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 e.inv hinv
    have pullAlong : ∀ {Z : Scheme.{u}} (q' : pullback f' f' ⟶ Z) (q : pullback f f ⟶ Z) (hq : GG ≫ q = q') (M : Z.Modules),
        (Scheme.Modules.pullback q').obj M ≅ (Scheme.Modules.pullback GG).obj ((Scheme.Modules.pullback q).obj M) := fun q' q hq M =>
      (Scheme.Modules.pullbackCongr hq.symm).app M ≪≫ ((Scheme.Modules.pullbackComp GG q).app M).symm
    have eM : (Scheme.Modules.pullback (addMor f' L')).obj ((Scheme.Modules.pullback e.inv).obj 𝓛) ≅
        (Scheme.Modules.pullback GG).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) :=
      (Scheme.Modules.pullbackComp (addMor f' L') e.inv).app 𝓛 ≪≫ pullAlong _ _ hmG.symm 𝓛
    have e1 : (Scheme.Modules.pullback (pullback.fst f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback e.inv).obj 𝓛)) ≅
        (Scheme.Modules.pullback GG).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛)) :=
      (Scheme.Modules.pullback _).mapIso ed.symm ≪≫ (Scheme.Modules.pullbackComp (pullback.fst f' f') e.inv).app _ ≪≫ pullAlong _ _ hGG1 _
    have e2 : (Scheme.Modules.pullback (pullback.snd f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback e.inv).obj 𝓛)) ≅
        (Scheme.Modules.pullback GG).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛)) :=
      (Scheme.Modules.pullback _).mapIso ed.symm ≪≫ (Scheme.Modules.pullbackComp (pullback.snd f' f') e.inv).app _ ≪≫ pullAlong _ _ hGG2 _
    have eΛ : mumfordBundle f' L' ((Scheme.Modules.pullback e.inv).obj 𝓛) ≅ (Scheme.Modules.pullback GG).obj (mumfordBundle f L 𝓛) :=
      (eM ⊗ᵢ (e1 ⊗ᵢ e2)) ≪≫ (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso GG _ _).symm) ≪≫
        (Scheme.Modules.pullbackTensorObjIso GG _ _).symm
    have along : ∀ (r' : pullback f' f' ⟶ pullback f' f') (r : pullback f f ⟶ pullback f f) (hr : r' ≫ GG = GG ≫ r),
        Nonempty ((Scheme.Modules.pullback r').obj (mumfordBundle f' L' ((Scheme.Modules.pullback e.inv).obj 𝓛)) ≅
          (Scheme.Modules.pullback GG).obj ((Scheme.Modules.pullback r).obj (mumfordBundle f L 𝓛))) := fun r' r hr =>
      ⟨(Scheme.Modules.pullback r').mapIso eΛ ≪≫ (Scheme.Modules.pullbackComp r' GG).app _ ≪≫
        (Scheme.Modules.pullbackCongr hr).app _ ≪≫ ((Scheme.Modules.pullbackComp GG r).app _).symm⟩
    have hr : pullback.lift (pullback.fst f' f') (pullback.snd f' f' ≫ act' b) (by rw [Category.assoc, act_over']; exact pullback.condition) ≫ GG = GG ≫ pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition) := by
      apply pullback.hom_ext
      · have l1 : (pullback.lift (pullback.fst f' f') (pullback.snd f' f' ≫ act' b) (by rw [Category.assoc, act_over']; exact pullback.condition) ≫ GG) ≫ pullback.fst f f = pullback.fst f' f' ≫ e.inv := by
          rw [Category.assoc, hGG1, ← Category.assoc, pullback.lift_fst]
        have l2 : (GG ≫ pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)) ≫ pullback.fst f f = pullback.fst f' f' ≫ e.inv := by
          rw [Category.assoc, pullback.lift_fst, hGG1]
        exact l1.trans l2.symm
      · have l1 : (pullback.lift (pullback.fst f' f') (pullback.snd f' f' ≫ act' b) (by rw [Category.assoc, act_over']; exact pullback.condition) ≫ GG) ≫ pullback.snd f f = pullback.snd f' f' ≫ act' b ≫ e.inv := by
          rw [Category.assoc, hGG2, ← Category.assoc, pullback.lift_snd, Category.assoc]
        have l2 : (GG ≫ pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)) ≫ pullback.snd f f = pullback.snd f' f' ≫ act' b ≫ e.inv := by
          rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hGG2, Category.assoc, ← hact']
        exact l1.trans l2.symm
    have hl : pullback.lift (pullback.fst f' f' ≫ act' (star b)) (pullback.snd f' f') (by rw [Category.assoc, act_over']; exact pullback.condition) ≫ GG = GG ≫ pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition) := by
      apply pullback.hom_ext
      · have l1 : (pullback.lift (pullback.fst f' f' ≫ act' (star b)) (pullback.snd f' f') (by rw [Category.assoc, act_over']; exact pullback.condition) ≫ GG) ≫ pullback.fst f f = pullback.fst f' f' ≫ act' (star b) ≫ e.inv := by
          rw [Category.assoc, hGG1, ← Category.assoc, pullback.lift_fst, Category.assoc]
        have l2 : (GG ≫ pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition)) ≫ pullback.fst f f = pullback.fst f' f' ≫ act' (star b) ≫ e.inv := by
          rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hGG1, Category.assoc, ← hact']
        exact l1.trans l2.symm
      · have l1 : (pullback.lift (pullback.fst f' f' ≫ act' (star b)) (pullback.snd f' f') (by rw [Category.assoc, act_over']; exact pullback.condition) ≫ GG) ≫ pullback.snd f f = pullback.snd f' f' ≫ e.inv := by
          rw [Category.assoc, hGG2, ← Category.assoc, pullback.lift_snd]
        have l2 : (GG ≫ pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f) (by rw [Category.assoc, act_over]; exact pullback.condition)) ≫ pullback.snd f f = pullback.snd f' f' ≫ e.inv := by
          rw [Category.assoc, pullback.lift_snd, hGG2]
        exact l1.trans l2.symm
    obtain ⟨er⟩ := along _ _ hr
    obtain ⟨el⟩ := along _ _ hl
    have key := LocIsoOnBase.pullback_of_comp_eq (pullback.fst f' f' ≫ f') GG (𝟙 _) (by rw [Category.comp_id]; exact hGGt) (hros b)
    have E := LocIsoOnBase.equivalence (pullback.fst f' f' ≫ f')
    exact E.trans (E.trans (locIsoOnBase_of_iso _ er) key) (locIsoOnBase_of_iso _ el.symm)

end S_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_inv_of_iso
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_pullback_inv_of_iso (solution)
