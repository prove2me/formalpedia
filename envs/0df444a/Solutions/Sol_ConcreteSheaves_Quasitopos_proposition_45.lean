-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.proposition_45
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:11:38.791417+00:00
-- url     : https://prove2.me/submissions/a28113db-799c-49b2-bd4b-cac935d1dd2f

import Theorems.Thm_ConcreteSheaves_Quasitopos_lemma_47
import Theorems.Thm_ConcreteSheaves_Quasitopos_lemma_49
import Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_39
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.Closed.Ideal
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits ConcreteSheaves.Quasitopos Opposite

universe u
variable {D : Type u} [SmallCategory D]

namespace ConcreteSheaves.Quasitopos.Proof45

private def concretizationMap (T : D) {P Q : Dᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    concretization T P ⟶ concretization T Q where
  app E := ↾(fun h => ⟨fun d => f.app (op T) (h.1 d), by
    obtain ⟨p, hp⟩ := h.2
    refine ⟨f.app E p, ?_⟩
    funext d
    exact (NatTrans.naturality_apply f d.op p).symm.trans
      (congrArg (f.app (op T)) (congrFun hp d))⟩)
  naturality := by
    intro E F g
    ext h
    rfl

private def concretizationFunctor (T : D) : (Dᵒᵖ ⥤ Type u) ⥤ (Dᵒᵖ ⥤ Type u) where
  obj := concretization T
  map := concretizationMap T
  map_id := by intro P; ext E h; rfl
  map_comp := by intro P Q R f g; ext E h; rfl

private def concretizationUnit (T : D) : 𝟭 (Dᵒᵖ ⥤ Type u) ⟶ concretizationFunctor T where
  app := concretizationπ T
  naturality := by
    intro P Q f
    ext E p
    apply Subtype.ext
    funext d
    exact (NatTrans.naturality_apply f d.op p).symm

/- Concretization preserves pullbacks whose base is concrete.  The base hypothesis is
essential: representatives of two point-functions must agree as plots in the base. -/
private theorem concretization_map_isPullback (T : D)
    {P X Y B : Dᵒᵖ ⥤ Type u} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (hB : IsConcrete T B)
    (h : IsPullback p q f g) :
    IsPullback ((concretizationFunctor T).map p) ((concretizationFunctor T).map q)
      ((concretizationFunctor T).map f) ((concretizationFunctor T).map g) := by
  apply IsPullback.of_forall_isPullback_app
  intro E
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun α => α.app E) ((concretizationFunctor T).map_commSq h.toCommSq).w
  · intro a b hab
    apply Subtype.ext
    funext d
    apply Types.ext_of_isPullback (h.app (op T))
    · exact congrFun (congrArg Subtype.val hab.1) d
    · exact congrFun (congrArg Subtype.val hab.2) d
  · rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ hxy
    have hplots : f.app E x = g.app E y := by
      apply hB E.unop
      funext d
      exact (NatTrans.naturality_apply f d.op x).symm.trans
        ((congrFun (congrArg Subtype.val hxy) d).trans
          (NatTrans.naturality_apply g d.op y))
    obtain ⟨z, hzx, hzy⟩ := Types.exists_of_isPullback (h.app E) x y hplots
    refine ⟨(concretizationπ T P).app E z, ?_, ?_⟩
    · apply Subtype.ext
      funext d
      change p.app (op T) (P.map d.op z) = X.map d.op x
      rw [NatTrans.naturality_apply, hzx]
    · apply Subtype.ext
      funext d
      change q.app (op T) (P.map d.op z) = Y.map d.op y
      rw [NatTrans.naturality_apply, hzy]


private noncomputable def reflectionFunctor (K : Coverage D) (T : D)
    (hT : IsTerminal T) (hK : IsConcreteSite K T hT) :
    (Dᵒᵖ ⥤ Type u) ⥤ DSpace K T :=
  (IsDSpace K T).lift (concretizationFunctor T ⋙ K.toGrothendieck.plusFunctor (Type u))
    (fun P => lemma_49 K T hT hK _ (lemma_47 K T hT hK P).1)

private noncomputable def reflectionUnit (K : Coverage D) (T : D)
    (hT : IsTerminal T) (hK : IsConcreteSite K T hT) :
    𝟭 (Dᵒᵖ ⥤ Type u) ⟶ reflectionFunctor K T hT hK ⋙ (IsDSpace K T).ι :=
  concretizationUnit T ≫ Functor.whiskerLeft (concretizationFunctor T)
    (K.toGrothendieck.toPlusNatTrans (Type u))

/- This is the same universal property as accepted Proposition 50, with the
functor made explicit so that preservation can be proved from its formula. -/
private noncomputable def reflectionAdjunction (K : Coverage D) (T : D)
    (hT : IsTerminal T) (hK : IsConcreteSite K T hT) :
    reflectionFunctor K T hT hK ⊣ (IsDSpace K T).ι := by
  classical
  let J := K.toGrothendieck
  let L := reflectionFunctor K T hT hK
  let η := reflectionUnit K T hT hK
  have sheaf (Q : DSpace K T) : Presheaf.IsSheaf J Q.obj := by
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
    intro X S hS
    exact Q.property.1 S hS
  have hu (P : Dᵒᵖ ⥤ Type u) (Q : DSpace K T) (f : P ⟶ Q.obj) :
      ∃! g : L.obj P ⟶ Q, η.app P ≫ g.hom = f := by
    obtain ⟨g₀, hg₀, unique⟩ := (lemma_47 K T hT hK P).2 Q.obj Q.property.2 f
    refine ⟨ObjectProperty.homMk (J.plusLift g₀ (sheaf Q)), ?_, ?_⟩
    · change (concretizationπ T P ≫ J.toPlus (concretization T P)) ≫
        J.plusLift g₀ (sheaf Q) = f
      rw [Category.assoc, J.toPlus_plusLift, hg₀]
    · intro g hg
      apply ObjectProperty.hom_ext
      apply J.plus_hom_ext _ _ (sheaf Q)
      change J.toPlus (concretization T P) ≫ g.hom =
        J.toPlus (concretization T P) ≫ J.plusLift g₀ (sheaf Q)
      rw [J.toPlus_plusLift]
      apply unique
      change (concretizationπ T P ≫ J.toPlus (concretization T P)) ≫ g.hom = f at hg
      exact (Category.assoc (concretizationπ T P)
        (J.toPlus (concretization T P)) g.hom).symm.trans hg
  let e (P : Dᵒᵖ ⥤ Type u) (Q : DSpace K T) :
      (L.obj P ⟶ Q) ≃ (P ⟶ Q.obj) :=
    Equiv.ofBijective (fun g => η.app P ≫ g.hom) (by
      constructor
      · intro a b hab
        obtain ⟨g, hg, huniq⟩ := hu P Q (η.app P ≫ a.hom)
        exact (huniq a rfl).trans (huniq b hab.symm).symm
      · intro f
        obtain ⟨g, hg, _⟩ := hu P Q f
        exact ⟨g, hg⟩)
  have he_left {P P' : Dᵒᵖ ⥤ Type u} {Q : DSpace K T}
      (f : P' ⟶ P) (g : L.obj P ⟶ Q) :
      e P' Q (L.map f ≫ g) = f ≫ e P Q g := by
    change η.app P' ≫ ((L.map f).hom ≫ g.hom) = f ≫ (η.app P ≫ g.hom)
    have hn : f ≫ η.app P = η.app P' ≫ (L.map f).hom := η.naturality f
    rw [← Category.assoc, ← hn, Category.assoc]
  exact Adjunction.mkOfHomEquiv {
    homEquiv := e
    homEquiv_naturality_left_symm := by
      intro P' P Q f g
      apply (e P' Q).injective
      rw [Equiv.apply_symm_apply, he_left, Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro P Q Q' g h
      change η.app P ≫ (g.hom ≫ h.hom) = (η.app P ≫ g.hom) ≫ h.hom
      exact (Category.assoc _ _ _).symm }

private theorem reflection_map_isPullback (K : Coverage D) (T : D)
    (hT : IsTerminal T) (hK : IsConcreteSite K T hT)
    {P X Y B : Dᵒᵖ ⥤ Type u} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (hB : IsConcrete T B)
    (h : IsPullback p q f g) :
    IsPullback ((reflectionFunctor K T hT hK).map p)
      ((reflectionFunctor K T hT hK).map q)
      ((reflectionFunctor K T hT hK).map f)
      ((reflectionFunctor K T hT hK).map g) := by
  apply IsPullback.of_map_of_faithful (IsDSpace K T).ι
  exact (concretization_map_isPullback T hB h).map
    (K.toGrothendieck.plusFunctor (Type u))

private theorem overPost_preservesBinaryProducts
    {C E : Type*} [Category* C] [Category* E] (F : C ⥤ E) (B : C)
    [HasBinaryProducts (Over B)]
    (h : ∀ {P X Y : C} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B},
      IsPullback p q f g → IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    PreservesLimitsOfShape (Discrete WalkingPair) (Over.post (X := B) F) := by
  let G := Over.post (X := B) F
  have hp (X Y : Over B) : PreservesLimit (pair X Y) G := by
    apply preservesLimit_of_preserves_limit_cone (prodIsProd X Y)
    refine (isLimitMapConeBinaryFanEquiv G _ _).symm ?_
    have hxy : IsPullback (F.map (prod.fst : X ⨯ Y ⟶ X).left)
        (F.map (prod.snd : X ⨯ Y ⟶ Y).left) (F.map X.hom) (F.map Y.hom) :=
      h (Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) (prod.snd : X ⨯ Y ⟶ Y)) (prodIsProd X Y))
    let lift (s : BinaryFan (G.obj X) (G.obj Y)) : s.pt ⟶ G.obj (X ⨯ Y) :=
      Over.homMk (hxy.lift s.fst.left s.snd.left (s.fst.w.trans s.snd.w.symm)) (by
        change hxy.lift _ _ _ ≫ F.map (X ⨯ Y).hom = s.pt.hom
        rw [← (prod.fst : X ⨯ Y ⟶ X).w, F.map_comp, ← Category.assoc]
        exact (congrArg (fun a => a ≫ F.map X.hom)
          (hxy.lift_fst _ _ _)).trans s.fst.w)
    refine BinaryFan.isLimitMk lift ?_ ?_ ?_
    · intro s
      apply Over.OverMorphism.ext
      exact hxy.lift_fst _ _ _
    · intro s
      apply Over.OverMorphism.ext
      exact hxy.lift_snd _ _ _
    · intro s m hm₁ hm₂
      apply Over.OverMorphism.ext
      apply hxy.hom_ext
      · exact (congrArg CommaMorphism.left hm₁).trans (hxy.lift_fst _ _ _).symm
      · exact (congrArg CommaMorphism.left hm₂).trans (hxy.lift_snd _ _ _).symm
  constructor
  intro K
  let := hp (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
  exact preservesLimit_of_iso_diagram G (diagramIsoPair K).symm

end ConcreteSheaves.Quasitopos.Proof45

open ConcreteSheaves.Quasitopos.Proof45

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    IsLocallyCartesianClosed (DSpace K T) := by
  classical
  let i := (IsDSpace K T).ι
  let L := reflectionFunctor K T hT hK
  let adj := reflectionAdjunction K T hT hK
  let : HasLimits (DSpace K T) := (proposition_39 K T hT hK).1
  intro B
  let I : Over B ⥤ Over (i.obj B) := Over.post i
  let LS := Over.post L ⋙ Over.map (adj.counit.app B)
  let : Reflective I := { L := LS, adj := Over.postAdjunctionRight adj }
  let : PreservesLimitsOfShape (Discrete WalkingPair) (Over.post (X := i.obj B) L) :=
    overPost_preservesBinaryProducts L (i.obj B)
      (fun h => reflection_map_isPullback K T hT hK B.property.2 h)
  let : IsIso (adj.counit.app B) := inferInstance
  let : PreservesLimitsOfShape (Discrete WalkingPair) (reflector I) := by
    change PreservesLimitsOfShape (Discrete WalkingPair) LS
    infer_instance
  let : CartesianMonoidalCategory (Over (i.obj B)) := Over.cartesianMonoidalCategory _
  let : CartesianMonoidalCategory (Over B) := Over.cartesianMonoidalCategory _
  let : MonoidalClosed (Over (i.obj B)) :=
    cartesianClosedOfEquiv (overEquivPresheafCostructuredArrow B.obj).symm
  let : ExponentialIdeal I := inferInstance
  let : MonoidalClosed (Over B) := cartesianClosedOfReflective I
  refine ⟨inferInstance, ?_⟩
  intro X
  exact Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd X)
