-- Prove2me | solution 1 for CategoryTheory.Sheaf.preservesInjectiveObjects_sheafCompose_uliftFunctor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/dd0619db-78a9-54cb-96e1-30a5798fd020

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CategoryTheory_Sheaf_preservesInjectiveObjects_sheafCompose_uliftFunctor

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits Opposite"

universe u

namespace G4

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

section SubA

variable {J}
variable (X₀ : Sheaf J AddCommGrpCat.{u}) {A : Sheaf J AddCommGrpCat.{u+1}}
  (i : A ⟶ (sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u}).obj X₀)

private theorem subA_injective [Mono i] (Y : Cᵒᵖ) : Function.Injective (i.hom.app Y) := by
  have h1 : Mono ((sheafToPresheaf J AddCommGrpCat.{u+1}).map i) := inferInstance
  have h2 : Mono (i.hom.app Y) := by
    have := (NatTrans.mono_iff_mono_app ((sheafToPresheaf J AddCommGrpCat.{u+1}).map i)).1 h1 Y
    exact this
  exact (AddCommGrpCat.mono_iff_injective _).1 h2

private def subA_S (Y : Cᵒᵖ) : AddSubgroup (X₀.obj.obj Y) :=
  (AddMonoidHom.range (i.hom.app Y).hom).comap
    (AddEquiv.ulift.symm : (X₀.obj.obj Y) ≃+ ULift.{u+1} (X₀.obj.obj Y)).toAddMonoidHom

private theorem mem_subA_S (Y : Cᵒᵖ) (x : X₀.obj.obj Y) :
    x ∈ subA_S X₀ i Y ↔ ∃ a : A.obj.obj Y, i.hom.app Y a = ULift.up x := Iff.rfl

private theorem subA_S_map {Y Y' : Cᵒᵖ} (f : Y ⟶ Y') (x : X₀.obj.obj Y) (hx : x ∈ subA_S X₀ i Y) :
    X₀.obj.map f x ∈ subA_S X₀ i Y' := by
  obtain ⟨a, ha⟩ := (mem_subA_S X₀ i Y x).1 hx
  refine (mem_subA_S X₀ i Y' _).2 ⟨A.obj.map f a, ?_⟩
  have := ConcreteCategory.congr_hom (i.hom.naturality f) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  rw [this, ha]
  rfl

private def subA_P : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj Y := AddCommGrpCat.of (subA_S X₀ i Y)
  map {Y Y'} f := AddCommGrpCat.ofHom
    ((X₀.obj.map f).hom.domRestrict (subA_S X₀ i Y) |>.codRestrict (subA_S X₀ i Y')
      (fun x => subA_S_map X₀ i f x.1 x.2))
  map_id Y := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp

private def subA_j : subA_P X₀ i ⟶ X₀.obj where
  app Y := AddCommGrpCat.ofHom (subA_S X₀ i Y).subtype
  naturality Y Y' f := by
    ext x
    rfl

private noncomputable def subA_equiv [Mono i] (Y : Cᵒᵖ) :
    A.obj.obj Y ≃+ ULift.{u+1} (subA_S X₀ i Y) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun a => ULift.up ⟨(i.hom.app Y a).down, (mem_subA_S X₀ i Y _).2 ⟨a, rfl⟩⟩)
      (fun a b => by
        apply ULift.ext; apply Subtype.ext
        simp only [map_add]
        rfl))
    (by
      constructor
      · intro a b h
        apply subA_injective X₀ i Y
        have h' := congrArg (fun z : ULift.{u+1} (subA_S X₀ i Y) => z.down.1) h
        exact ULift.ext _ _ h'
      · rintro ⟨⟨x, hx⟩⟩
        obtain ⟨a, ha⟩ := (mem_subA_S X₀ i Y x).1 hx
        refine ⟨a, ?_⟩
        apply ULift.ext; apply Subtype.ext
        show (i.hom.app Y a).down = x
        rw [ha])

private theorem subA_equiv_apply [Mono i] (Y : Cᵒᵖ) (a : A.obj.obj Y) :
    ((subA_equiv X₀ i Y a).down : X₀.obj.obj Y) = (i.hom.app Y a).down := rfl

private theorem subA_U_map_down {Y Y' : Cᵒᵖ} (f : Y ⟶ Y')
    (z : ((sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u}).obj X₀).obj.obj Y) :
    ((((sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u}).obj X₀).obj.map f) z).down =
      X₀.obj.map f z.down := rfl

private theorem subA_ulift_map_down {P Q : AddCommGrpCat.{u}} (g : P ⟶ Q)
    (z : AddCommGrpCat.uliftFunctor.{u+1, u}.obj P) :
    ((AddCommGrpCat.uliftFunctor.{u+1, u}.map g) z).down = g z.down := rfl

private theorem subA_P_map_val {Y Y' : Cᵒᵖ} (f : Y ⟶ Y') (w : subA_S X₀ i Y) :
    (((subA_P X₀ i).map f) w : subA_S X₀ i Y').1 = X₀.obj.map f w.1 := rfl

private theorem subA_iso_hom_apply [Mono i] (Y : Cᵒᵖ) (a : A.obj.obj Y) :
    (((AddEquiv.toAddCommGrpIso (X := A.obj.obj Y)
        (Y := (subA_P X₀ i ⋙ AddCommGrpCat.uliftFunctor.{u+1, u}).obj Y) (subA_equiv X₀ i Y)).hom a).down :
        subA_S X₀ i Y).1 = (i.hom.app Y a).down := rfl

private noncomputable def subA_iso [Mono i] :
    A.obj ≅ subA_P X₀ i ⋙ AddCommGrpCat.uliftFunctor.{u+1, u} :=
  NatIso.ofComponents (fun Y => (subA_equiv X₀ i Y).toAddCommGrpIso) (by
    intro Y Y' f
    ext a
    apply ULift.ext; apply Subtype.ext
    simp only [ConcreteCategory.comp_apply, Functor.comp_map]
    have := ConcreteCategory.congr_hom (i.hom.naturality f) a
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    have h2 : ((i.hom.app Y') (A.obj.map f a)).down = X₀.obj.map f ((i.hom.app Y) a).down := by
      rw [this]; rfl
    erw [subA_ulift_map_down, subA_P_map_val, subA_iso_hom_apply, subA_iso_hom_apply, h2])

private theorem subA_isSheaf [Mono i] : Presheaf.IsSheaf J (subA_P X₀ i) :=
  Presheaf.isSheaf_of_isSheaf_comp J _ AddCommGrpCat.uliftFunctor.{u+1, u}
    ((Presheaf.isSheaf_of_iso_iff (subA_iso X₀ i)).1 A.property)

theorem exists_preimage_subsheaf (X₀ : Sheaf J AddCommGrpCat.{u}) {A : Sheaf J AddCommGrpCat.{u+1}}
    (i : A ⟶ (sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u}).obj X₀) [Mono i] :
    ∃ (A₀ : Sheaf J AddCommGrpCat.{u}) (j : A₀ ⟶ X₀)
      (e : (sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u}).obj A₀ ≅ A),
      Mono j ∧ e.hom ≫ i = (sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u}).map j := by
  let A₀ : Sheaf J AddCommGrpCat.{u} := ⟨subA_P X₀ i, subA_isSheaf X₀ i⟩
  let j : A₀ ⟶ X₀ := ⟨subA_j X₀ i⟩

  let e' : (sheafToPresheaf J _).obj ((sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u}).obj A₀) ≅
      (sheafToPresheaf J _).obj A := (subA_iso X₀ i).symm
  let e : (sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u}).obj A₀ ≅ A :=
    (fullyFaithfulSheafToPresheaf J _).preimageIso e'
  refine ⟨A₀, j, e, ?_, ?_⟩
  ·
    haveI : ∀ Y, Mono ((subA_j X₀ i).app Y) := fun Y =>
      (AddCommGrpCat.mono_iff_injective _).2 (fun a b h => Subtype.ext h)
    haveI : Mono (subA_j X₀ i) := NatTrans.mono_of_mono_app _
    exact Sheaf.Hom.mono_of_presheaf_mono J _ j
  ·
    refine (Iso.eq_inv_comp e).1 ?_
    apply (sheafToPresheaf J _).map_injective
    have he : (sheafToPresheaf J _).map e.inv = (subA_iso X₀ i).hom := by
      show (sheafToPresheaf J _).map ((fullyFaithfulSheafToPresheaf J _).preimageIso e').inv = _
      rw [Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.map_preimage]
      rfl
    rw [Functor.map_comp, he]
    ext Y a
    rfl

end SubA

end G4

namespace G4

variable {C : Type u} [SmallCategory C]

noncomputable def freePsh (X : C) : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yoneda.obj X ⋙ AddCommGrpCat.free

private theorem freePsh_map_of (X : C) {Y Y' : Cᵒᵖ} (h : Y ⟶ Y') (f : unop Y ⟶ X) :
    (freePsh X).map h (FreeAbelianGroup.of f) = FreeAbelianGroup.of (h.unop ≫ f) := by
  simp [freePsh]
  exact FreeAbelianGroup.map_of_apply _

private theorem freePsh_ulift_map_up (X : C) {Y Y' : Cᵒᵖ} (h : Y ⟶ Y')
    (x : FreeAbelianGroup (unop Y ⟶ X)) :
    (freePsh X ⋙ AddCommGrpCat.uliftFunctor.{u+1, u}).map h (ULift.up x) =
      ULift.up ((freePsh X).map h x) := rfl

private noncomputable def freePshDesc {X : C} {P : Cᵒᵖ ⥤ AddCommGrpCat.{u+1}} (s : P.obj (op X))
    (Y : Cᵒᵖ) : ULift.{u+1} (FreeAbelianGroup (unop Y ⟶ X)) →+ P.obj Y :=
  (FreeAbelianGroup.lift (fun f : unop Y ⟶ X => P.map f.op s)).comp
    (AddEquiv.ulift : ULift.{u+1} (FreeAbelianGroup (unop Y ⟶ X)) ≃+ _).toAddMonoidHom

private theorem freePshDesc_up_of {X : C} {P : Cᵒᵖ ⥤ AddCommGrpCat.{u+1}} (s : P.obj (op X))
    (Y : Cᵒᵖ) (f : unop Y ⟶ X) :
    freePshDesc s Y (ULift.up (FreeAbelianGroup.of f)) = P.map f.op s := by
  show FreeAbelianGroup.lift (fun f : unop Y ⟶ X => P.map f.op s) (FreeAbelianGroup.of f) = _
  exact FreeAbelianGroup.lift_apply_of _ _

private theorem ulift_free_hom_ext {α : Type u} {B : Type (u+1)} [AddCommGroup B]
    {g₁ g₂ : ULift.{u+1} (FreeAbelianGroup α) →+ B}
    (h : ∀ x : α, g₁ (ULift.up (FreeAbelianGroup.of x)) = g₂ (ULift.up (FreeAbelianGroup.of x))) :
    g₁ = g₂ := by
  have : g₁.comp (AddEquiv.ulift.symm : FreeAbelianGroup α ≃+ ULift.{u+1} (FreeAbelianGroup α)).toAddMonoidHom =
      g₂.comp (AddEquiv.ulift.symm : FreeAbelianGroup α ≃+ ULift.{u+1} (FreeAbelianGroup α)).toAddMonoidHom := by
    ext x
    exact h x
  ext ⟨x⟩
  exact DFunLike.congr_fun this x

noncomputable def freePshUliftHomEquiv {X : C} {P : Cᵒᵖ ⥤ AddCommGrpCat.{u+1}} :
    (freePsh X ⋙ AddCommGrpCat.uliftFunctor.{u+1, u} ⟶ P) ≃ P.obj (op X) where
  toFun φ := φ.app (op X) (ULift.up (FreeAbelianGroup.of (𝟙 X)))
  invFun s :=
    { app := fun Y => AddCommGrpCat.ofHom (freePshDesc s Y)
      naturality := fun Y Y' h => by
        apply AddCommGrpCat.hom_ext
        apply ulift_free_hom_ext
        intro f
        show freePshDesc s Y' ((freePsh X ⋙ AddCommGrpCat.uliftFunctor.{u+1, u}).map h
            (ULift.up (FreeAbelianGroup.of f))) = P.map h (freePshDesc s Y (ULift.up (FreeAbelianGroup.of f)))
        rw [freePsh_ulift_map_up, freePsh_map_of]
        erw [freePshDesc_up_of, freePshDesc_up_of]
        rw [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply] }
  left_inv φ := by
    apply NatTrans.ext; funext Y
    apply AddCommGrpCat.hom_ext
    apply ulift_free_hom_ext
    intro f
    show freePshDesc (φ.app (op X) (ULift.up (FreeAbelianGroup.of (𝟙 X)))) Y
        (ULift.up (FreeAbelianGroup.of f)) = φ.app Y (ULift.up (FreeAbelianGroup.of f))
    erw [freePshDesc_up_of]
    have := ConcreteCategory.congr_hom (φ.naturality f.op) (ULift.up (FreeAbelianGroup.of (𝟙 X)))
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [freePsh_ulift_map_up, freePsh_map_of] at this
    refine this.symm.trans ?_
    simp only [Quiver.Hom.unop_op, Category.comp_id]
  right_inv s := by
    show freePshDesc s (op X) (ULift.up (FreeAbelianGroup.of (𝟙 X))) = s
    erw [freePshDesc_up_of]
    simp

theorem freePshUliftHomEquiv_apply {X : C} {P : Cᵒᵖ ⥤ AddCommGrpCat.{u+1}}
    (φ : freePsh X ⋙ AddCommGrpCat.uliftFunctor.{u+1, u} ⟶ P) :
    freePshUliftHomEquiv φ = φ.app (op X) (ULift.up (FreeAbelianGroup.of (𝟙 X))) := rfl

theorem freePshUliftHomEquiv_comp {X : C} {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u+1}}
    (φ : freePsh X ⋙ AddCommGrpCat.uliftFunctor.{u+1, u} ⟶ P) (f : P ⟶ Q) :
    freePshUliftHomEquiv (φ ≫ f) = f.app (op X) (freePshUliftHomEquiv φ) := rfl

theorem isSeparating_freePsh_ulift {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u+1}} (f g : P ⟶ Q)
    (h : ∀ (X : C) (φ : freePsh X ⋙ AddCommGrpCat.uliftFunctor.{u+1, u} ⟶ P), φ ≫ f = φ ≫ g) :
    f = g := by
  ext Y s
  obtain ⟨φ, rfl⟩ := (freePshUliftHomEquiv (X := unop Y) (P := P)).surjective s
  show f.app (op (unop Y)) (freePshUliftHomEquiv φ) = g.app (op (unop Y)) (freePshUliftHomEquiv φ)
  rw [← freePshUliftHomEquiv_comp, ← freePshUliftHomEquiv_comp, h]

section SubC

variable {J : GrothendieckTopology C}

theorem isSeparator_map_sigmaObj [HasWeakSheafify J AddCommGrpCat.{u+1}]
    (U : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u+1})
    (S : C → Sheaf J AddCommGrpCat.{u}) [HasCoproduct S]
    (e : ∀ X : C, U.obj (S X) ≅
      (presheafToSheaf J AddCommGrpCat.{u+1}).obj (freePsh X ⋙ AddCommGrpCat.uliftFunctor.{u+1, u})) :
    IsSeparator (U.obj (∐ S)) := by
  rw [isSeparator_def]
  intro F F' f g hfg

  have key : ∀ (X : C) (k : U.obj (S X) ⟶ F), k ≫ f = k ≫ g := by
    intro X k
    have hk : k = U.map (Sigma.ι S X) ≫ (U.map (retraction (Sigma.ι S X)) ≫ k) := by
      rw [← Category.assoc, ← U.map_comp, IsSplitMono.id, U.map_id, Category.id_comp]
    rw [hk]
    simp only [Category.assoc]
    congr 1
    rw [← Category.assoc, hfg, Category.assoc]

  refine (sheafToPresheaf J AddCommGrpCat.{u+1}).map_injective
    (isSeparating_freePsh_ulift _ _ (fun X φ => ?_))
  apply ((sheafificationAdjunction J AddCommGrpCat.{u+1}).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_right_symm]
  have := key X ((e X).hom ≫ ((sheafificationAdjunction J AddCommGrpCat.{u+1}).homEquiv _ _).symm φ)
  simpa only [Category.assoc, Iso.cancel_iso_hom_left] using this

end SubC

end G4

namespace G4

section Instances

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

theorem preservesFilteredColimitsOfSize_forget :
    PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u+1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u+1, u+1, u, u} _

attribute [local instance] preservesFilteredColimitsOfSize_forget

theorem isGrothendieckAbelian_sheaf_ulift :
    IsGrothendieckAbelian.{u+1} (Sheaf J AddCommGrpCat.{u+1}) where

theorem preservesSheafification_uliftFunctor :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{u+1, u} :=
  @GrothendieckTopology.instPreservesSheafification C _ J AddCommGrpCat.{u} AddCommGrpCat.{u+1} _ _
    AddCommGrpCat.uliftFunctor.{u+1, u} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Instances

section Main

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

attribute [local instance] preservesFilteredColimitsOfSize_forget
  isGrothendieckAbelian_sheaf_ulift preservesSheafification_uliftFunctor

noncomputable abbrev U : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u+1} :=
  sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u}

noncomputable def freeShf (X : C) : Sheaf J AddCommGrpCat.{u} :=
  (presheafToSheaf J AddCommGrpCat.{u}).obj (freePsh X)

noncomputable def freeShfIso (X : C) :
    (U J).obj (freeShf J X) ≅
      (presheafToSheaf J AddCommGrpCat.{u+1}).obj (freePsh X ⋙ AddCommGrpCat.uliftFunctor.{u+1, u}) :=
  ((sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{u+1, u}
    (sheafificationAdjunction J AddCommGrpCat.{u}) (sheafificationAdjunction J AddCommGrpCat.{u+1})).app
      (freePsh X)).symm

theorem hasColimitsOfShape_discrete_sheaf :
    HasColimitsOfShape (Discrete C) (Sheaf J AddCommGrpCat.{u}) :=
  Sheaf.instHasColimitsOfShape

attribute [local instance] hasColimitsOfShape_discrete_sheaf

noncomputable def G₀ : Sheaf J AddCommGrpCat.{u} := ∐ freeShf J

theorem isSeparator_U_G₀ : IsSeparator ((U J).obj (G₀ J)) :=
  isSeparator_map_sigmaObj (U J) (freeShf J) (freeShfIso J)

theorem preservesInjectiveObjects_U : (U J).PreservesInjectiveObjects where
  injective_obj {I} hI := by
    rw [injective_iff_rlp_monomorphisms_zero,
      ← IsGrothendieckAbelian.generatingMonomorphisms_rlp (isSeparator_U_G₀ J)]
    rintro _ _ _ ⟨A'⟩
    obtain ⟨A₀, j, e, hj, he⟩ := exists_preimage_subsheaf (J := J) (G₀ J) A'.arrow

    refine ⟨fun {a b} sq => ?_⟩
    obtain ⟨g₀, hg₀⟩ := hI.factors ((U J).preimage (e.hom ≫ a)) j
    refine CommSq.HasLift.mk' ⟨(U J).map g₀, ?_, ?_⟩
    · have hA : A'.arrow = e.inv ≫ (U J).map j := by
        rw [← he, Iso.inv_hom_id_assoc]
      rw [hA, Category.assoc, ← Functor.map_comp, hg₀, Functor.map_preimage, Iso.inv_hom_id_assoc]
    · exact (isZero_zero _).eq_of_tgt _ _

end Main

end G4

theorem solution
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    (sheafCompose J AddCommGrpCat.uliftFunctor.{u+1, u} :
      Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u+1}).PreservesInjectiveObjects :=
  G4.preservesInjectiveObjects_U J

end S_CategoryTheory_Sheaf_preservesInjectiveObjects_sheafCompose_uliftFunctor
end P2MW
export P2MW.S_CategoryTheory_Sheaf_preservesInjectiveObjects_sheafCompose_uliftFunctor (solution)
