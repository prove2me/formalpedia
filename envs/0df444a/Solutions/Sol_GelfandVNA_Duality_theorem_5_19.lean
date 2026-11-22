-- Prove2me | solution 1 for GelfandVNA.Duality.theorem_5_19
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:26:17.451242+00:00
-- url     : https://prove2.me/submissions/1a287bed-590e-4ae6-9bca-2a376400ed60

import Mathlib
import Definitions.Def_GelfandVNA_Duality_Locales
import Definitions.Def_GelfandVNA_Duality_EMS
import Theorems.Thm_GelfandVNA_Duality_proposition_4_54
import Theorems.Thm_GelfandVNA_Duality_lemma_5_11
import Definitions.Def_GelfandVNA_Duality_Spaces
import Theorems.Thm_GelfandVNA_Duality_proposition_2_72
import Theorems.Thm_GelfandVNA_Duality_proposition_2_73
import Theorems.Thm_GelfandVNA_Duality_proposition_5_4
import Theorems.Thm_GelfandVNA_Duality_proposition_5_16

/-!
Theorem 5.19 of Pavlov, *Gelfand-type duality for commutative von Neumann algebras*
(arXiv:2005.05284v3, p. 45). Part A: the pull-back `f ↦ f*` on `M/N` and the functor `ML`.
-/

namespace GelfandVNA.Duality.T519

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

universe u

/-! ### The quotient `M/N` and the pull-back -/

lemma MmodN.exists_rep {X : Type u} {E : Enhanced X} (q : MmodN E) :
    ∃ (m : Set X) (hm : m ∈ E.measurable), MmodN.mk m hm = q :=
  Quotient.inductionOn (motive := fun q : Quotient (nullSetoid E) =>
    ∃ (m : Set X) (hm : m ∈ E.measurable), MmodN.mk m hm = q) q (fun a => ⟨a.1, a.2, rfl⟩)

lemma mk_le_mk {X : Type u} {E : Enhanced X} {a b : Set X} (ha : a ∈ E.measurable)
    (hb : b ∈ E.measurable) : MmodN.mk a ha ≤ MmodN.mk b hb ↔ a \ b ∈ E.negligible :=
  Iff.rfl

lemma mk_congr {X : Type u} {E : Enhanced X} {a b : Set X} (h : a = b) (ha : a ∈ E.measurable)
    (hb : b ∈ E.measurable) : MmodN.mk a ha = MmodN.mk b hb := by
  subst h
  rfl

lemma mk_eq_mk {X : Type u} {E : Enhanced X} {a b : Set X} (ha : a ∈ E.measurable)
    (hb : b ∈ E.measurable) (h : (a \ b) ∪ (b \ a) ∈ E.negligible) :
    MmodN.mk a ha = MmodN.mk b hb :=
  Quotient.sound h

lemma pullPremap_mk {X Y : Type u} {E : Enhanced X} {F : Enhanced Y} (f : Premap E F)
    (m : Set Y) (hm : m ∈ F.measurable) :
    pullPremap f (MmodN.mk m hm) = MmodN.mk (partialPreimage f.1 m) (f.2.2.1 _ hm) :=
  rfl

lemma pp_sdiff {X Y : Type u} (f : X → Option Y) (s t : Set Y) :
    partialPreimage f (s \ t) = partialPreimage f s \ partialPreimage f t := by
  ext x
  constructor
  · rintro ⟨y, ⟨hys, hyt⟩, hxy⟩
    refine ⟨⟨y, hys, hxy⟩, ?_⟩
    rintro ⟨y', hy', hxy'⟩
    rw [hxy] at hxy'
    cases hxy'
    exact hyt hy'
  · rintro ⟨⟨y, hys, hxy⟩, hn⟩
    exact ⟨y, ⟨hys, fun hyt => hn ⟨y, hyt, hxy⟩⟩, hxy⟩

lemma pullPremap_mono {X Y : Type u} {E : Enhanced X} {F : Enhanced Y} (g : Premap E F) :
    Monotone (pullPremap g) := by
  intro a b hab
  obtain ⟨a0, ha0, rfl⟩ := MmodN.exists_rep a
  obtain ⟨b0, hb0, rfl⟩ := MmodN.exists_rep b
  rw [pullPremap_mk, pullPremap_mk, mk_le_mk, ← pp_sdiff]
  exact g.2.2.2 _ ((mk_le_mk ha0 hb0).1 hab)

/-- The class of a premap in `EMS`. -/
def homOf {A B : EMS.{u}} (g : Premap A.E B.E) : A ⟶ B :=
  Quot.mk (weakHomRelation A.E B.E) g

lemma hom_ind {A B : EMS.{u}} {P : (A ⟶ B) → Prop} (h : ∀ g : Premap A.E B.E, P (homOf g))
    (F : A ⟶ B) : P F :=
  Quot.inductionOn (motive := fun F : Quot (weakHomRelation A.E B.E) => P F) F h

lemma pullHom_homOf {A B : EMS.{u}} (g : Premap A.E B.E) : pullHom (homOf g) = pullPremap g :=
  rfl

lemma homOf_comp {A B C : EMS.{u}} (f : Premap A.E B.E) (g : Premap B.E C.E) :
    homOf f ≫ homOf g = homOf (compPremap f g) :=
  rfl

lemma pullHom_id (A : EMS.{u}) : pullHom (𝟙 A) = id := by
  funext q
  obtain ⟨m, hm, rfl⟩ := MmodN.exists_rep q
  show pullPremap (idPremap A.E) (MmodN.mk m hm) = MmodN.mk m hm
  rw [pullPremap_mk]
  exact mk_congr (partialPreimage_id m) _ _

lemma pullHom_comp {A B C : EMS.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    pullHom (f ≫ g) = pullHom f ∘ pullHom g := by
  refine hom_ind (P := fun f => pullHom (f ≫ g) = pullHom f ∘ pullHom g) (fun f' => ?_) f
  refine hom_ind (P := fun g => pullHom (homOf f' ≫ g) = pullHom (homOf f') ∘ pullHom g)
    (fun g' => ?_) g
  rw [homOf_comp, pullHom_homOf, pullHom_homOf, pullHom_homOf]
  funext q
  obtain ⟨m, hm, rfl⟩ := MmodN.exists_rep q
  show pullPremap (compPremap f' g') (MmodN.mk m hm) =
    pullPremap f' (pullPremap g' (MmodN.mk m hm))
  rw [pullPremap_mk, pullPremap_mk, pullPremap_mk]
  exact mk_congr (partialPreimage_comp g'.1 f'.1 m) _ _

lemma pullHom_comp_apply {A B C : EMS.{u}} (f : A ⟶ B) (g : B ⟶ C) (q : MmodN C.E) :
    pullHom (f ≫ g) q = pullHom f (pullHom g q) :=
  congrFun (pullHom_comp f g) q

lemma pullHom_mono {A B : EMS.{u}} (f : A ⟶ B) : Monotone (pullHom f) :=
  hom_ind (P := fun f => Monotone (pullHom f)) (fun g => pullPremap_mono g) f

lemma pullHom_injective {A B : EMS.{u}} (f g : A ⟶ B) (h : pullHom f = pullHom g) : f = g := by
  revert h
  refine hom_ind (P := fun f => pullHom f = pullHom g → f = g) (fun f' => ?_) f
  refine hom_ind (P := fun g => pullHom (homOf f') = pullHom g → homOf f' = g) (fun g' => ?_) g
  intro h
  apply Quot.sound
  intro s hs
  have h' : (Quotient.mk (nullSetoid A.E) ⟨partialPreimage f'.1 s, f'.2.2.1 _ hs⟩ : MmodN A.E) =
      Quotient.mk (nullSetoid A.E) ⟨partialPreimage g'.1 s, g'.2.2.1 _ hs⟩ :=
    congrFun h (MmodN.mk s hs)
  exact Quotient.exact h'

lemma pull_inv_hom {A B : EMS.{u}} (θ : A ≅ B) (q : MmodN B.E) :
    pullHom θ.inv (pullHom θ.hom q) = q := by
  rw [← pullHom_comp_apply, θ.inv_hom_id, pullHom_id]
  rfl

lemma pull_hom_inv {A B : EMS.{u}} (θ : A ≅ B) (q : MmodN A.E) :
    pullHom θ.hom (pullHom θ.inv q) = q := by
  rw [← pullHom_comp_apply, θ.hom_inv_id, pullHom_id]
  rfl

/-- An isomorphism of `EMS` induces an order isomorphism of the quotients `M/N`. -/
noncomputable def pullIso {A B : EMS.{u}} (θ : A ≅ B) : MmodN B.E ≃o MmodN A.E where
  toFun := pullHom θ.hom
  invFun := pullHom θ.inv
  left_inv := pull_inv_hom θ
  right_inv := pull_hom_inv θ
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      have h' : pullHom θ.inv (pullHom θ.hom a) ≤ pullHom θ.inv (pullHom θ.hom b) :=
        pullHom_mono θ.inv h
      rwa [pull_inv_hom, pull_inv_hom] at h'
    · exact fun h => pullHom_mono θ.hom h

lemma pullIso_apply {A B : EMS.{u}} (θ : A ≅ B) (q : MmodN B.E) :
    pullIso θ q = pullHom θ.hom q := rfl

lemma pullIso_symm_apply {A B : EMS.{u}} (θ : A ≅ B) (q : MmodN A.E) :
    (pullIso θ).symm q = pullHom θ.inv q := rfl

/-! ### Transport of a supremum-preserving map along order isomorphisms -/

/-- A map between posets with the three properties of Lemma 5.11 becomes a map of frames after
transport along order isomorphisms onto frames. -/
noncomputable def transportHom {P Q L M : Type u} [PartialOrder P] [PartialOrder Q]
    [Order.Frame L] [Order.Frame M] (eP : P ≃o L) (eQ : Q ≃o M) (F : P → Q)
    (h1 : ∀ a b c : P, IsGLB {a, b} c → IsGLB {F a, F b} (F c))
    (h2 : ∀ a : P, IsGreatest Set.univ a → IsGreatest Set.univ (F a))
    (h3 : ∀ (s : Set P) (a : P), IsLUB s a → IsLUB (F '' s) (F a)) : FrameHom L M where
  toFun b := eQ (F (eP.symm b))
  map_inf' a b := by
    have h := (eP.symm.isGLB_image' (s := {a, b}) (x := a ⊓ b)).2 isGLB_pair
    rw [Set.image_pair] at h
    have h' := (eQ.isGLB_image' (s := {F (eP.symm a), F (eP.symm b)})
      (x := F (eP.symm (a ⊓ b)))).2 (h1 _ _ _ h)
    rw [Set.image_pair] at h'
    exact h'.unique isGLB_pair
  map_top' := by
    have h : IsGreatest Set.univ (eP.symm ⊤) :=
      ⟨Set.mem_univ _, fun x _ => (eP.le_symm_apply).2 le_top⟩
    have h' := (h2 _ h).2 (Set.mem_univ (eQ.symm ⊤))
    exact top_unique ((eQ.symm_apply_le).1 h')
  map_sSup' s := by
    have h := (eP.symm.isLUB_image' (s := s) (x := sSup s)).2 (isLUB_sSup s)
    have h' := (eQ.isLUB_image' (s := F '' (eP.symm '' s)) (x := F (eP.symm (sSup s)))).2
      (h3 _ _ h)
    rw [Set.image_image, Set.image_image] at h'
    exact h'.unique (isLUB_sSup _)

lemma transportHom_apply {P Q L M : Type u} [PartialOrder P] [PartialOrder Q]
    [Order.Frame L] [Order.Frame M] (eP : P ≃o L) (eQ : Q ≃o M) (F : P → Q)
    (h1 : ∀ a b c : P, IsGLB {a, b} c → IsGLB {F a, F b} (F c))
    (h2 : ∀ a : P, IsGreatest Set.univ a → IsGreatest Set.univ (F a))
    (h3 : ∀ (s : Set P) (a : P), IsLUB s a → IsLUB (F '' s) (F a)) (b : L) :
    transportHom eP eQ F h1 h2 h3 b = eQ (F (eP.symm b)) := rfl

/-! ### Morphisms of `MLoc` -/

lemma mloc_hom_ext {A B : MLoc.{u}} (f g : A ⟶ B)
    (h : ∀ b, MLoc.frameHom f b = MLoc.frameHom g b) : f = g := by
  apply InducedCategory.hom_ext
  apply Quiver.Hom.unop_inj
  apply Frm.hom_ext
  exact FrameHom.ext h

lemma frameHom_id (A : MLoc.{u}) (b : A.carrier) : MLoc.frameHom (𝟙 A) b = b := rfl

lemma frameHom_comp {A B C : MLoc.{u}} (f : A ⟶ B) (g : B ⟶ C) (c : C.carrier) :
    MLoc.frameHom (f ≫ g) c = MLoc.frameHom f (MLoc.frameHom g c) := rfl

/-- The morphism of `MLoc` given by a map of frames. -/
def mlocHomMk {A B : MLoc.{u}} (φ : FrameHom B.carrier A.carrier) : A ⟶ B :=
  InducedCategory.homMk (Frm.ofHom φ).op

lemma frameHom_mlocHomMk {A B : MLoc.{u}} (φ : FrameHom B.carrier A.carrier) :
    MLoc.frameHom (mlocHomMk φ) = φ := rfl

/-- An isomorphism of `MLoc` gives an order isomorphism of the underlying algebras. -/
def mlocOrderIso {A B : MLoc.{u}} (θ : A ≅ B) : B.carrier ≃o A.carrier where
  toFun := MLoc.frameHom θ.hom
  invFun := MLoc.frameHom θ.inv
  left_inv b := by
    rw [← frameHom_comp, θ.inv_hom_id, frameHom_id]
  right_inv a := by
    rw [← frameHom_comp, θ.hom_inv_id, frameHom_id]
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      have h' : MLoc.frameHom θ.inv (MLoc.frameHom θ.hom a) ≤
          MLoc.frameHom θ.inv (MLoc.frameHom θ.hom b) :=
        OrderHomClass.mono (MLoc.frameHom θ.inv) h
      rwa [← frameHom_comp, ← frameHom_comp, θ.inv_hom_id, frameHom_id, frameHom_id] at h'
    · exact fun h => OrderHomClass.mono (MLoc.frameHom θ.hom) h

/-- An order isomorphism of the underlying algebras gives an isomorphism of `MLoc`. -/
def mlocIsoMk {A B : MLoc.{u}} (e : B.carrier ≃o A.carrier) : A ≅ B where
  hom := mlocHomMk (e : FrameHom B.carrier A.carrier)
  inv := mlocHomMk (e.symm : FrameHom A.carrier B.carrier)
  hom_inv_id := by
    apply mloc_hom_ext
    intro b
    rw [frameHom_comp, frameHom_mlocHomMk, frameHom_mlocHomMk, frameHom_id]
    exact e.apply_symm_apply b
  inv_hom_id := by
    apply mloc_hom_ext
    intro b
    rw [frameHom_comp, frameHom_mlocHomMk, frameHom_mlocHomMk, frameHom_id]
    exact e.symm_apply_apply b

/-! ### The functor `ML` -/

lemma exists_alg (A : CSLEMS.{u}) : ∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
    HasFiniteValuationCover B ∧ Nonempty (MmodN A.obj.E ≃o B) :=
  proposition_4_54 A.obj.E A.property.2

/-- A localizable complete Boolean algebra order-isomorphic to `M/N` (Proposition 4.54). -/
noncomputable def alg (A : CSLEMS.{u}) : Type u := (exists_alg A).choose

noncomputable instance algCBA (A : CSLEMS.{u}) : CompleteBooleanAlgebra (alg A) :=
  (exists_alg A).choose_spec.choose

lemma alg_localizable (A : CSLEMS.{u}) : HasFiniteValuationCover (alg A) :=
  (exists_alg A).choose_spec.choose_spec.1

/-- The order isomorphism `M/N ≃ alg A`. -/
noncomputable def κ (A : CSLEMS.{u}) : MmodN A.obj.E ≃o alg A :=
  (exists_alg A).choose_spec.choose_spec.2.some

/-- `ML` on objects. -/
noncomputable def mlObj (A : CSLEMS.{u}) : MLoc.{u} :=
  show MLocObj.{u} from { carrier := alg A, localizable := alg_localizable A }

/-- The order isomorphism `ι` of the statement. -/
noncomputable def ιML (A : CSLEMS.{u}) : (mlObj A).carrier ≃o MmodN A.obj.E := (κ A).symm

/-- `ML` on morphisms, as a map of frames: this is Lemma 5.11. -/
noncomputable def mlHom {A B : CSLEMS.{u}} (f : A ⟶ B) :
    FrameHom (mlObj B).carrier (mlObj A).carrier :=
  transportHom (κ B) (κ A) (pullHom f.hom) (lemma_5_11 f).1 (lemma_5_11 f).2.1 (lemma_5_11 f).2.2

lemma mlHom_apply {A B : CSLEMS.{u}} (f : A ⟶ B) (b : (mlObj B).carrier) :
    mlHom f b = κ A (pullHom f.hom ((κ B).symm b)) := rfl

/-- The functor `ML : CSLEMS ⥤ MLoc` (Definition 5.10). -/
noncomputable def mlFunctor : CSLEMS.{u} ⥤ MLoc.{u} where
  obj := mlObj
  map f := mlocHomMk (mlHom f)
  map_id A := by
    apply mloc_hom_ext
    intro b
    rw [frameHom_mlocHomMk, frameHom_id, mlHom_apply]
    have h : (𝟙 A : A ⟶ A).hom = 𝟙 A.obj := rfl
    rw [h, pullHom_id]
    exact (κ A).apply_symm_apply b
  map_comp {A B C} f g := by
    apply mloc_hom_ext
    intro c
    rw [frameHom_comp, frameHom_mlocHomMk, frameHom_mlocHomMk, frameHom_mlocHomMk, mlHom_apply,
      mlHom_apply, mlHom_apply]
    have h : (f ≫ g).hom = f.hom ≫ g.hom := rfl
    rw [h, pullHom_comp_apply, OrderIso.symm_apply_apply]

lemma mlFunctor_map_frameHom {A B : CSLEMS.{u}} (f : A ⟶ B) (b : (mlObj B).carrier) :
    MLoc.frameHom (mlFunctor.map f) b = κ A (pullHom f.hom ((κ B).symm b)) := rfl

instance mlFunctor_faithful : (mlFunctor.{u}).Faithful where
  map_injective {A B} f g h := by
    apply ObjectProperty.hom_ext
    apply pullHom_injective
    funext q
    have h1 : MLoc.frameHom (mlFunctor.map f) (κ B q) = MLoc.frameHom (mlFunctor.map g) (κ B q) := by
      rw [h]
    have h2 : κ A (pullHom f.hom ((κ B).symm (κ B q))) =
        κ A (pullHom g.hom ((κ B).symm (κ B q))) := h1
    rw [OrderIso.symm_apply_apply] at h2
    exact (κ A).injective h2

end GelfandVNA.Duality.T519

/-!
Theorem 5.19, part B: the enhanced measurable space `TM(X)` of a compact Hausdorff extremally
disconnected space, the Stone spectrum of a complete Boolean algebra, and hyperstonean spaces.
-/

namespace GelfandVNA.Duality.T519

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
open Set Topology TopologicalSpace

universe u

/-! ### `TM(X)`: clopen representatives -/

section TopSpace

variable {X : Type u} [TopologicalSpace X]

lemma tm_meas_of_isOpen {v : Set X} (hv : IsOpen v) : v ∈ (TM X).measurable :=
  ⟨v, hv, by
    rw [symmDiff_self, Set.bot_eq_empty]
    exact IsMeagre.empty⟩

/-- In a Baire space a meagre open set is empty. -/
lemma eq_empty_of_isOpen_isMeagre [BaireSpace X] {U : Set X} (hU : IsOpen U) (hm : IsMeagre U) :
    U = ∅ := by
  have hd : Dense Uᶜ := dense_of_mem_residual hm
  have hc : IsClosed Uᶜ := hU.isClosed_compl
  have h : Uᶜ = univ := by
    rw [← hc.closure_eq]
    exact hd.closure_eq
  exact Set.compl_univ_iff.1 h

lemma mk_le_mk_clopen [BaireSpace X] {C D : Set X} (hC : IsClopen C) (hD : IsClopen D) :
    MmodN.mk C (tm_meas_of_isOpen hC.isOpen) ≤ MmodN.mk D (tm_meas_of_isOpen hD.isOpen) ↔
      C ⊆ D := by
  rw [mk_le_mk]
  constructor
  · intro h
    have hopen : IsOpen (C \ D) := hC.isOpen.sdiff hD.isClosed
    exact Set.sdiff_eq_empty.1 (eq_empty_of_isOpen_isMeagre hopen h)
  · intro h
    rw [Set.sdiff_eq_empty.2 h]
    exact IsMeagre.empty

/-- Every class of `TM(X)` has a clopen representative when `X` is extremally disconnected
(Lemma 2.68). -/
lemma exists_clopen_rep [ExtremallyDisconnected X] (q : MmodN (TM X)) :
    ∃ (K : Set X) (hK : IsClopen K), q = MmodN.mk K (tm_meas_of_isOpen hK.isOpen) := by
  obtain ⟨s, hs, rfl⟩ := MmodN.exists_rep q
  obtain ⟨v, hv, hsv⟩ := hs
  have hK : IsClopen (closure v) := ⟨isClosed_closure, ExtremallyDisconnected.open_closure v hv⟩
  refine ⟨closure v, hK, ?_⟩
  apply mk_eq_mk
  have h1 : s =ᶠ[residual X] v := (isMeagre_symmDiff_iff _ _).1 hsv
  have h2 : closure v =ᶠ[residual X] v := closure_residualEq hv.isLocallyClosed
  have h3 : IsMeagre (symmDiff s (closure v)) := (isMeagre_symmDiff_iff _ _).2 (h1.trans h2.symm)
  exact h3

end TopSpace

/-! ### Premaps from continuous maps (Lemma 5.3) -/

lemma partialPreimage_some {X Y : Type u} (f : X → Y) (s : Set Y) :
    partialPreimage (fun x => some (f x)) s = f ⁻¹' s := by
  ext x
  simp [partialPreimage]

/-- A continuous map whose preimages of closed nowhere dense sets are nowhere dense is a premap
`TM(X) → TM(Y)`. -/
lemma isPremap_of_continuous {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (σ : X → Y)
    (hσ : Continuous σ)
    (hnd : ∀ V : Set Y, IsClosed V → interior V = ∅ → interior (σ ⁻¹' V) = ∅) :
    IsPremap (TM X) (TM Y) (fun x => some (σ x)) := by
  have hmeagre : ∀ s : Set Y, IsMeagre s → IsMeagre (σ ⁻¹' s) := by
    intro s hs
    obtain ⟨S, hSnd, hSc, hsS⟩ := isMeagre_iff_countable_union_isNowhereDense.1 hs
    refine isMeagre_iff_countable_union_isNowhereDense.2
      ⟨(fun t => σ ⁻¹' t) '' S, ?_, hSc.image _, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      have h1 : interior (σ ⁻¹' closure t) = ∅ := hnd _ isClosed_closure (hSnd t ht)
      have h2 : closure (σ ⁻¹' t) ⊆ σ ⁻¹' closure t := hσ.closure_preimage_subset t
      exact Set.subset_empty_iff.1 ((interior_mono h2).trans h1.subset)
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := hsS hx
      exact ⟨σ ⁻¹' t, ⟨t, ht, rfl⟩, hxt⟩
  refine ⟨?_, fun s hs => ?_, fun s hs => ?_⟩
  · have h : (partialDomain (fun x : X => some (σ x)))ᶜ = ∅ := by
      ext x
      simp [partialDomain]
    rw [h]
    exact IsMeagre.empty
  · rw [partialPreimage_some]
    obtain ⟨v, hv, hsv⟩ := hs
    exact ⟨σ ⁻¹' v, hv.preimage hσ, hmeagre _ hsv⟩
  · rw [partialPreimage_some]
    exact hmeagre s hs

/-! ### The Stone spectrum of a Boolean algebra -/

section Stone

variable {B : Type u} [BooleanAlgebra B]

/-- A point of the Stone spectrum as a homomorphism `B → 2`. -/
def ev (p : stoneSpectrum B) : BoundedLatticeHom B Bool := p

/-- The basic clopen set of points `p` with `p b = 1`. -/
def basic (b : B) : Set (stoneSpectrum B) := {p | ev p b = true}

lemma basic_top : basic (⊤ : B) = univ := by
  ext p
  show ev p ⊤ = true ↔ True
  rw [map_top]
  decide

lemma basic_bot : basic (⊥ : B) = ∅ := by
  ext p
  show ev p ⊥ = true ↔ False
  rw [map_bot]
  decide

lemma basic_inf (a b : B) : basic (a ⊓ b) = basic a ∩ basic b := by
  ext p
  show ev p (a ⊓ b) = true ↔ ev p a = true ∧ ev p b = true
  rw [map_inf]
  cases ev p a <;> cases ev p b <;> decide

lemma basic_sup (a b : B) : basic (a ⊔ b) = basic a ∪ basic b := by
  ext p
  show ev p (a ⊔ b) = true ↔ ev p a = true ∨ ev p b = true
  rw [map_sup]
  cases ev p a <;> cases ev p b <;> decide

lemma basic_compl (b : B) : basic bᶜ = (basic b)ᶜ := by
  ext p
  show ev p bᶜ = true ↔ ¬ ev p b = true
  rw [map_compl']
  cases ev p b <;> decide

lemma basic_isOpen (b : B) : IsOpen (basic b) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨b, rfl⟩

lemma basic_isClosed (b : B) : IsClosed (basic b) := by
  apply isOpen_compl_iff.mp
  rw [← basic_compl]
  exact basic_isOpen _

lemma basic_isClopen (b : B) : IsClopen (basic b) := ⟨basic_isClosed b, basic_isOpen b⟩

lemma basic_mono {a b : B} (hab : a ≤ b) : basic a ⊆ basic b := by
  intro p hp
  have h : basic a = basic a ∩ basic b := by rw [← basic_inf, inf_eq_left.2 hab]
  rw [h] at hp
  exact hp.2

open Classical in
/-- A two-valued homomorphism from a predicate that respects the lattice operations. -/
noncomputable def homOfPred (P : B → Prop) (hsup : ∀ a c, P (a ⊔ c) ↔ P a ∨ P c)
    (hinf : ∀ a c, P (a ⊓ c) ↔ P a ∧ P c) (htop : P ⊤) (hbot : ¬ P ⊥) :
    BoundedLatticeHom B Bool where
  toFun b := decide (P b)
  map_sup' a c := by
    by_cases ha : P a <;> by_cases hc : P c <;> simp [hsup, ha, hc]
  map_inf' a c := by
    by_cases ha : P a <;> by_cases hc : P c <;> simp [hinf, ha, hc]
  map_top' := by simp [htop]
  map_bot' := by simp [hbot]

open Classical in
lemma homOfPred_apply (P : B → Prop) (hsup : ∀ a c, P (a ⊔ c) ↔ P a ∨ P c)
    (hinf : ∀ a c, P (a ⊓ c) ↔ P a ∧ P c) (htop : P ⊤) (hbot : ¬ P ⊥) (b : B) :
    homOfPred P hsup hinf htop hbot b = true ↔ P b := by
  show decide (P b) = true ↔ P b
  simp

/-- The Boolean prime ideal theorem: a nonzero element lies in some point of the spectrum. -/
lemma basic_nonempty {b : B} (hb : b ≠ ⊥) : (basic b).Nonempty := by
  have hd : Disjoint (Order.PFilter.principal b : Set B)
      (Order.Ideal.principal (⊥ : B) : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hxb
    have h1 : b ≤ x := hx
    have h2 : x ≤ ⊥ := hxb
    exact hb (le_bot_iff.1 (h1.trans h2))
  obtain ⟨J, hJ, -, hdis⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hd
  have hbJ : b ∉ J := fun h => Set.disjoint_left.1 hdis (le_refl b) h
  refine ⟨homOfPred (fun a => a ∉ J) ?_ ?_ ?_ ?_, ?_⟩
  · intro a c
    rw [Order.Ideal.sup_mem_iff]
    tauto
  · intro a c
    have hi : a ⊓ c ∈ J ↔ a ∈ J ∨ c ∈ J :=
      ⟨hJ.mem_or_mem, fun h => h.elim (J.lower inf_le_left) (J.lower inf_le_right)⟩
    rw [hi]
    tauto
  · exact hJ.toIsProper.top_notMem
  · exact fun h => h J.bot_mem
  · exact (homOfPred_apply _ _ _ _ _ b).2 hbJ

lemma basic_subset_iff {a b : B} : basic a ⊆ basic b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    have hne : a ⊓ bᶜ ≠ ⊥ := by
      rw [← _root_.sdiff_eq]
      exact fun hz => hn (_root_.sdiff_eq_bot_iff.1 hz)
    obtain ⟨p, hp⟩ := basic_nonempty hne
    rw [basic_inf, basic_compl] at hp
    exact hp.2 (h hp.1)
  · exact basic_mono

lemma basic_basis : IsTopologicalBasis {U : Set (stoneSpectrum B) | ∃ b : B, U = basic b} := by
  have hb := isTopologicalBasis_of_subbasis_of_inter
    (r := {U : Set (stoneSpectrum B) | ∃ b : B, U = basic b}) rfl
    (by
      rintro s ⟨a, rfl⟩ t ⟨b, rfl⟩
      exact ⟨a ⊓ b, (basic_inf a b).symm⟩)
  have hu : (univ : Set (stoneSpectrum B)) ∈ {U | ∃ b : B, U = basic b} := ⟨⊤, basic_top.symm⟩
  simpa only [insert_eq_of_mem hu] using hb

lemma exists_basic_of_mem_open {U : Set (stoneSpectrum B)} {p : stoneSpectrum B}
    (hp : p ∈ U) (hU : IsOpen U) : ∃ b : B, p ∈ basic b ∧ basic b ⊆ U := by
  obtain ⟨V, ⟨b, rfl⟩, hp, hV⟩ := basic_basis.exists_subset_of_mem_open hp hU
  exact ⟨b, hp, hV⟩

instance stone_t2 : T2Space (stoneSpectrum B) := by
  refine ⟨fun p q hpq => ?_⟩
  have hex : ∃ b, ev p b ≠ ev q b := by
    by_contra hcon
    push Not at hcon
    exact hpq (DFunLike.ext (ev p) (ev q) hcon)
  obtain ⟨b, hb⟩ := hex
  rcases hp : ev p b with _ | _ <;> rcases hq : ev q b with _ | _
  · exact absurd (hp.trans hq.symm) hb
  · refine ⟨basic bᶜ, basic b, basic_isOpen _, basic_isOpen _, ?_, hq, ?_⟩
    · rw [basic_compl]
      intro h
      have h' : ev p b = true := h
      rw [hp] at h'
      cases h'
    · rw [basic_compl]
      exact disjoint_compl_left
  · refine ⟨basic b, basic bᶜ, basic_isOpen _, basic_isOpen _, hp, ?_, ?_⟩
    · rw [basic_compl]
      intro h
      have h' : ev q b = true := h
      rw [hq] at h'
      cases h'
    · rw [basic_compl]
      exact disjoint_compl_right
  · exact absurd (hp.trans hq.symm) hb

instance stone_compact : CompactSpace (stoneSpectrum B) := by
  refine ⟨isCompact_iff_ultrafilter_le_nhds.2 (fun 𝔘 _ => ?_)⟩
  have h1 : ∀ a c : B, basic (a ⊔ c) ∈ 𝔘 ↔ basic a ∈ 𝔘 ∨ basic c ∈ 𝔘 := by
    intro a c
    rw [basic_sup]
    exact Ultrafilter.union_mem_iff
  have h2 : ∀ a c : B, basic (a ⊓ c) ∈ 𝔘 ↔ basic a ∈ 𝔘 ∧ basic c ∈ 𝔘 := by
    intro a c
    rw [basic_inf]
    exact Filter.inter_mem_iff
  have h3 : basic (⊤ : B) ∈ 𝔘 := by
    rw [basic_top]
    exact Filter.univ_mem
  have h4 : ¬ basic (⊥ : B) ∈ 𝔘 := by
    rw [basic_bot]
    exact fun h => Filter.empty_notMem (𝔘 : Filter (stoneSpectrum B)) h
  let p : stoneSpectrum B := homOfPred (fun b => basic b ∈ 𝔘) h1 h2 h3 h4
  have hp : ∀ b : B, p ∈ basic b → basic b ∈ 𝔘 := fun b hb =>
    (homOfPred_apply (fun b => basic b ∈ 𝔘) h1 h2 h3 h4 b).1 hb
  refine ⟨p, Set.mem_univ _, ?_⟩
  have hn : 𝓝 p = ⨅ s ∈ {s | p ∈ s ∧ s ∈ {U : Set (stoneSpectrum B) | ∃ b : B, U = basic b}},
      Filter.principal s := TopologicalSpace.nhds_generateFrom
  rw [hn]
  refine le_iInf₂ (fun s hs => ?_)
  obtain ⟨hps, b, rfl⟩ := hs
  rw [Filter.le_principal_iff]
  exact hp b hps

end Stone

/-! ### The Stone spectrum of a complete Boolean algebra -/

section StoneComplete

variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Completeness makes closures of open sets basic clopen sets. -/
lemma closure_eq_basic {U : Set (stoneSpectrum B)} (hU : IsOpen U) :
    closure U = basic (sSup {b : B | basic b ⊆ U}) := by
  have hUb : U ⊆ basic (sSup {b : B | basic b ⊆ U}) := by
    intro p hp
    obtain ⟨c, hpc, hc⟩ := exists_basic_of_mem_open hp hU
    exact basic_mono (le_sSup hc) hpc
  apply subset_antisymm (closure_minimal hUb (basic_isClosed _))
  intro p hp
  by_contra hpU
  obtain ⟨c, hpc, hc⟩ := exists_basic_of_mem_open
    (show p ∈ basic (sSup {b : B | basic b ⊆ U}) ∩ (closure U)ᶜ from ⟨hp, hpU⟩)
    ((basic_isOpen _).inter isClosed_closure.isOpen_compl)
  have hcb : c ≤ sSup {b : B | basic b ⊆ U} := basic_subset_iff.1 (fun _ hx => (hc hx).1)
  have hdis : c ⊓ sSup {b : B | basic b ⊆ U} = ⊥ := by
    rw [inf_sSup_eq]
    simp only [iSup_eq_bot]
    intro a ha
    by_contra hne
    obtain ⟨q, hq⟩ := basic_nonempty hne
    rw [basic_inf] at hq
    exact (hc hq.1).2 (subset_closure (ha hq.2))
  have hzero : c = ⊥ := by
    rw [← inf_eq_left.2 hcb]
    exact hdis
  rw [hzero, basic_bot] at hpc
  exact hpc

instance stone_extremallyDisconnected : ExtremallyDisconnected (stoneSpectrum B) :=
  ⟨fun U hU => by
    rw [closure_eq_basic hU]
    exact basic_isOpen _⟩

/-- `b ↦ [basic b]` as an order embedding of `B` into `M/N` of `TM(Sp B)`. -/
noncomputable def stoneEmb : B ↪o MmodN (TM (stoneSpectrum B)) :=
  OrderEmbedding.ofMapLEIff
    (fun b => MmodN.mk (basic b) (tm_meas_of_isOpen (basic_isOpen b)))
    (fun a b => by
      rw [mk_le_mk_clopen (basic_isClopen a) (basic_isClopen b)]
      exact basic_subset_iff)

lemma stoneEmb_surjective : Function.Surjective (stoneEmb (B := B)) := by
  intro q
  obtain ⟨K, hK, rfl⟩ := exists_clopen_rep q
  have h : basic (sSup {b : B | basic b ⊆ K}) = K := by
    rw [← closure_eq_basic hK.isOpen, hK.isClosed.closure_eq]
  exact ⟨sSup {b : B | basic b ⊆ K}, mk_congr h _ _⟩

/-- The Loomis–Sikorski isomorphism `B ≃ M/N` for `TM(Sp B)`. -/
noncomputable def stoneIso : B ≃o MmodN (TM (stoneSpectrum B)) :=
  OrderIso.ofSurjective stoneEmb stoneEmb_surjective

lemma stoneIso_apply (b : B) :
    stoneIso b = MmodN.mk (basic b) (tm_meas_of_isOpen (basic_isOpen b)) := rfl

end StoneComplete

/-! ### The Stone map of a complete homomorphism -/

section StoneMap

/-- The map of spectra `p ↦ p ∘ φ`. -/
noncomputable def stoneMap {B B' : Type u} [BooleanAlgebra B] [BooleanAlgebra B'] (φ : BoundedLatticeHom B' B) :
    stoneSpectrum B → stoneSpectrum B' := fun p => (ev p).comp φ

lemma stoneMap_preimage_basic {B B' : Type u} [BooleanAlgebra B] [BooleanAlgebra B']
    (φ : BoundedLatticeHom B' B) (b' : B') : stoneMap φ ⁻¹' basic b' = basic (φ b') := rfl

lemma stoneMap_continuous {B B' : Type u} [BooleanAlgebra B] [BooleanAlgebra B']
    (φ : BoundedLatticeHom B' B) : Continuous (stoneMap φ) := by
  apply continuous_generateFrom_iff.2
  rintro _ ⟨b', rfl⟩
  exact basic_isOpen (φ b')

/-- A map of frames between complete Boolean algebras as a bounded lattice homomorphism. -/
noncomputable def frameToBLH {B B' : Type u} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra B']
    (φ : FrameHom B' B) : BoundedLatticeHom B' B where
  toFun := φ
  map_sup' := map_sup φ
  map_inf' := map_inf φ
  map_top' := map_top φ
  map_bot' := map_bot φ

lemma frameToBLH_apply {B B' : Type u} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra B']
    (φ : FrameHom B' B) (b' : B') : frameToBLH φ b' = φ b' := rfl

/-- The Stone map of a complete homomorphism pulls closed nowhere dense sets back to nowhere dense
sets. -/
lemma stoneMap_nd {B B' : Type u} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra B']
    (φ : FrameHom B' B) (V : Set (stoneSpectrum B')) (hV : IsClosed V) (hint : interior V = ∅) :
    interior (stoneMap (frameToBLH φ) ⁻¹' V) = ∅ := by
  by_contra hne
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨b, hpb, hb⟩ := exists_basic_of_mem_open hp isOpen_interior
  have hbne : b ≠ ⊥ := by
    rintro rfl
    rw [basic_bot] at hpb
    exact hpb
  have hW : closure Vᶜ = univ := (interior_eq_empty_iff_dense_compl.1 hint).closure_eq
  rw [closure_eq_basic hV.isOpen_compl] at hW
  have hD : sSup {d : B' | basic d ⊆ Vᶜ} = ⊤ :=
    top_unique (basic_subset_iff.1 (by
      rw [hW]
      exact Set.subset_univ _))
  have hφ : sSup (φ '' {d : B' | basic d ⊆ Vᶜ}) = ⊤ := by
    have h : φ (sSup {d : B' | basic d ⊆ Vᶜ}) = sSup (φ '' {d : B' | basic d ⊆ Vᶜ}) :=
      map_sSup φ _
    rw [← h, hD, map_top]
  have hzero : b ⊓ sSup (φ '' {d : B' | basic d ⊆ Vᶜ}) = ⊥ := by
    rw [inf_sSup_eq]
    simp only [iSup_eq_bot]
    rintro _ ⟨d, hd, rfl⟩
    by_contra hne'
    obtain ⟨q, hq⟩ := basic_nonempty hne'
    rw [basic_inf] at hq
    have h1 : q ∈ stoneMap (frameToBLH φ) ⁻¹' V := interior_subset (hb hq.1)
    have h2 : stoneMap (frameToBLH φ) q ∈ basic d := hq.2
    exact hd h2 h1
  rw [hφ, inf_top_eq] at hzero
  exact hbne hzero

/-- `Spec` on morphisms: the premap `TM(Sp B) → TM(Sp B')` of a complete homomorphism
`φ : B' → B`. -/
noncomputable def stonePremap {B B' : Type u} [CompleteBooleanAlgebra B]
    [CompleteBooleanAlgebra B'] (φ : FrameHom B' B) :
    Premap (TM (stoneSpectrum B)) (TM (stoneSpectrum B')) :=
  ⟨fun p => some (stoneMap (frameToBLH φ) p),
    isPremap_of_continuous _ (stoneMap_continuous _) (stoneMap_nd φ)⟩

lemma pull_stonePremap {B B' : Type u} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra B']
    (φ : FrameHom B' B) (b' : B') : pullPremap (stonePremap φ) (stoneIso b') = stoneIso (φ b') := by
  rw [stoneIso_apply, stoneIso_apply, pullPremap_mk]
  apply mk_congr
  show partialPreimage (fun p => some (stoneMap (frameToBLH φ) p)) (basic b') = basic (φ b')
  rw [partialPreimage_some, stoneMap_preimage_basic]
  rfl

end StoneMap

/-! ### Hyperstonean spaces -/

section HStoneanSpace

variable {X : Type u} [TopologicalSpace X]

lemma opens_coe_compl (a : Opens X) : ((aᶜ : Opens X) : Set X) = interior ((a : Set X)ᶜ) := by
  apply subset_antisymm
  · apply interior_maximal _ (aᶜ).isOpen
    intro x hx hxa
    have h : x ∈ ((aᶜ ⊓ a : Opens X) : Set X) := by
      rw [Opens.coe_inf]
      exact ⟨hx, hxa⟩
    rw [(disjoint_compl_left (a := a)).eq_bot, Opens.coe_bot] at h
    exact h
  · have hdisj : Disjoint (⟨interior ((a : Set X)ᶜ), isOpen_interior⟩ : Opens X) a := by
      rw [disjoint_iff_inf_le]
      intro x hx
      obtain ⟨h1, h2⟩ := hx
      exact (interior_subset h1 h2).elim
    exact le_compl_iff_disjoint_right.2 hdisj

lemma closure_coe_eq (a : Opens X) (h : aᶜ ⊔ aᶜᶜ = ⊤) :
    closure (a : Set X) = ((aᶜᶜ : Opens X) : Set X) := by
  rw [closure_eq_compl_interior_compl, ← opens_coe_compl]
  apply subset_antisymm
  · intro x hx
    have hx' : x ∈ ((aᶜ ⊔ aᶜᶜ : Opens X) : Set X) := by
      rw [h, Opens.coe_top]
      exact Set.mem_univ x
    rw [Opens.coe_sup] at hx'
    rcases hx' with hx' | hx'
    · exact absurd hx' hx
    · exact hx'
  · intro x hx hx'
    have h2 : x ∈ ((aᶜᶜ ⊓ aᶜ : Opens X) : Set X) := by
      rw [Opens.coe_inf]
      exact ⟨hx, hx'⟩
    rw [(disjoint_compl_left (a := aᶜ)).eq_bot, Opens.coe_bot] at h2
    exact h2

lemma extremallyDisconnected_of_opens (h : ∀ a : Opens X, aᶜ ⊔ aᶜᶜ = ⊤) :
    ExtremallyDisconnected X := by
  refine ⟨fun U hU => ?_⟩
  have hc : closure U = (((⟨U, hU⟩ : Opens X)ᶜᶜ : Opens X) : Set X) :=
    closure_coe_eq (⟨U, hU⟩ : Opens X) (h _)
  rw [hc]
  exact (((⟨U, hU⟩ : Opens X)ᶜᶜ : Opens X)).isOpen

lemma regularSpace_of_opens (h : IsRegularLocale (Opens X)) : RegularSpace X := by
  refine RegularSpace.of_exists_mem_nhds_isClosed_subset (fun x s hs => ?_)
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.1 hs
  have ha := h (⟨U, hU⟩ : Opens X)
  have hx : x ∈ sSup {b : Opens X | bᶜ ⊔ (⟨U, hU⟩ : Opens X) = ⊤} := by
    rw [← ha]
    exact hxU
  obtain ⟨b, hb, hxb⟩ := Opens.mem_sSup.1 hx
  refine ⟨closure (b : Set X), mem_nhds_iff.2 ⟨b, subset_closure, b.isOpen, hxb⟩,
    isClosed_closure, ?_⟩
  intro y hy
  have hy' : y ∈ (((bᶜ ⊔ (⟨U, hU⟩ : Opens X) : Opens X)) : Set X) := by
    rw [hb, Opens.coe_top]
    exact Set.mem_univ y
  rw [Opens.coe_sup] at hy'
  rcases hy' with hy' | hy'
  · rw [opens_coe_compl, closure_eq_compl_interior_compl] at *
    exact absurd hy' hy
  · exact hUs hy'

lemma isCompactElement_orderIso {P Q : Type u} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q)
    {k : P} (hk : IsCompactElement k) : IsCompactElement (e k) := by
  intro s v hne hdir hlub hle
  have hlub' : IsLUB (e.symm '' s) (e.symm v) := (e.symm.isLUB_image').2 hlub
  have hdir' : DirectedOn (· ≤ ·) (e.symm '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨e.symm z, ⟨z, hz, rfl⟩, e.symm.monotone hxz, e.symm.monotone hyz⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, hkx⟩ := hk (e.symm '' s) (e.symm v) (hne.image _) hdir' hlub'
    ((e.le_symm_apply).2 hle)
  exact ⟨x, hx, (e.le_symm_apply).1 hkx⟩

lemma isCompactElement_iff_isClopen [CompactSpace X] [T2Space X] (a : Opens X) :
    IsCompactElement a ↔ IsClopen (a : Set X) := by
  rw [Opens.isCompactElement_iff]
  exact ⟨fun h => ⟨h.isClosed, a.isOpen⟩, fun h => h.1.isCompact⟩

end HStoneanSpace

lemma hstonean_compact (S : HStonean.{u}) : CompactSpace S.toTop := by
  have h := (Opens.isCompactElement_iff (⊤ : Opens S.toTop)).1 S.hyperstonean.1.1.1.1
  rw [Opens.coe_top] at h
  exact isCompact_univ_iff.1 h

lemma hstonean_extremallyDisconnected (S : HStonean.{u}) : ExtremallyDisconnected S.toTop :=
  extremallyDisconnected_of_opens S.hyperstonean.1.2

lemma hstonean_t2 (S : HStonean.{u}) : T2Space S.toTop := by
  have : RegularSpace S.toTop := regularSpace_of_opens S.hyperstonean.1.1.2
  infer_instance

/-- An isomorphism of locales gives an order isomorphism of the frames of opens. -/
def localeOrderIso {P Q : Type u} [Order.Frame P] [Order.Frame Q]
    (θ : Locale.of P ≅ Locale.of Q) : Q ≃o P where
  toFun := θ.hom.unop.hom
  invFun := θ.inv.unop.hom
  left_inv q := by
    show (θ.inv ≫ θ.hom).unop.hom q = q
    rw [θ.inv_hom_id]
    rfl
  right_inv p := by
    show (θ.hom ≫ θ.inv).unop.hom p = p
    rw [θ.hom_inv_id]
    rfl
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      have h' : θ.inv.unop.hom (θ.hom.unop.hom a) ≤ θ.inv.unop.hom (θ.hom.unop.hom b) :=
        OrderHomClass.mono θ.inv.unop.hom h
      have ha : θ.inv.unop.hom (θ.hom.unop.hom a) = a := by
        show (θ.inv ≫ θ.hom).unop.hom a = a
        rw [θ.inv_hom_id]
        rfl
      have hb : θ.inv.unop.hom (θ.hom.unop.hom b) = b := by
        show (θ.inv ≫ θ.hom).unop.hom b = b
        rw [θ.inv_hom_id]
        rfl
      rwa [ha, hb] at h'
    · exact fun h => OrderHomClass.mono θ.hom.unop.hom h

end GelfandVNA.Duality.T519

/-!
Theorem 5.19, part C: `ML` is full and essentially surjective, hence an equivalence.
-/

namespace GelfandVNA.Duality.T519

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
open Set Topology TopologicalSpace

universe u

/-! ### Fullness: lifting a complete homomorphism to a point map -/

/-- Every map of frames `M'/N' → M/N` between objects of `CSLEMS` is induced by a morphism. -/
lemma exists_lift {A A' : CSLEMS.{u}} (Φ : mlObj A ⟶ mlObj A') :
    ∃ f : A ⟶ A', mlFunctor.map f = Φ := by
  obtain ⟨C, instC, -, ⟨θ⟩⟩ := proposition_5_16 A
  obtain ⟨C', instC', -, ⟨θ'⟩⟩ := proposition_5_16 A'
  -- the algebras `C`, `C'` of the two spectra, identified with `alg A`, `alg A'`
  let α : C ≃o alg A := (stoneIso.trans (pullIso θ)).trans (κ A)
  let α' : C' ≃o alg A' := (stoneIso.trans (pullIso θ')).trans (κ A')
  have hα : ∀ c : C, α c = κ A (pullHom θ.hom (stoneIso c)) := fun _ => rfl
  have hα' : ∀ c : C', α' c = κ A' (pullHom θ'.hom (stoneIso c)) := fun _ => rfl
  -- the transported complete homomorphism `C' → C`
  let φ : FrameHom C' C :=
    ((α.symm : FrameHom (alg A) C).comp (MLoc.frameHom Φ)).comp (α' : FrameHom C' (alg A'))
  have hφ : ∀ c : C', α (φ c) = MLoc.frameHom Φ (α' c) := fun c => α.apply_symm_apply _
  -- the morphism of `EMS`
  let g : EMS.of (stoneSpectrum C) (TM (stoneSpectrum C)) ⟶
      EMS.of (stoneSpectrum C') (TM (stoneSpectrum C')) :=
    homOf (A := EMS.of (stoneSpectrum C) (TM (stoneSpectrum C)))
      (B := EMS.of (stoneSpectrum C') (TM (stoneSpectrum C'))) (stonePremap φ)
  have hg : ∀ c : C', pullHom g (stoneIso c) = stoneIso (φ c) := fun c => pull_stonePremap φ c
  refine ⟨ObjectProperty.homMk (θ.hom ≫ g ≫ θ'.inv), ?_⟩
  apply mloc_hom_ext
  intro b
  obtain ⟨c, rfl⟩ := α'.surjective b
  have e1 : (κ A').symm (α' c) = pullHom θ'.hom (stoneIso c) := (κ A').symm_apply_apply _
  have e3 : pullHom θ'.inv (pullHom θ'.hom (stoneIso c)) = stoneIso c := pull_inv_hom θ' _
  have e2 : pullHom (θ.hom ≫ g ≫ θ'.inv) (pullHom θ'.hom (stoneIso c)) =
      pullHom θ.hom (stoneIso (φ c)) :=
    calc pullHom (θ.hom ≫ g ≫ θ'.inv) (pullHom θ'.hom (stoneIso c))
        = pullHom θ.hom (pullHom (g ≫ θ'.inv) (pullHom θ'.hom (stoneIso c))) :=
          pullHom_comp_apply _ _ _
      _ = pullHom θ.hom (pullHom g (pullHom θ'.inv (pullHom θ'.hom (stoneIso c)))) :=
          congrArg (pullHom θ.hom) (pullHom_comp_apply _ _ _)
      _ = pullHom θ.hom (pullHom g (stoneIso c)) :=
          congrArg (fun x => pullHom θ.hom (pullHom g x)) e3
      _ = pullHom θ.hom (stoneIso (φ c)) := congrArg (pullHom θ.hom) (hg c)
  have key : κ A (pullHom (θ.hom ≫ g ≫ θ'.inv) ((κ A').symm (α' c))) =
      MLoc.frameHom Φ (α' c) :=
    (congrArg (fun x => κ A (pullHom (θ.hom ≫ g ≫ θ'.inv) x)) e1).trans
      ((congrArg (κ A) e2).trans ((hα (φ c)).symm.trans (hφ c)))
  exact key

instance mlFunctor_full : (mlFunctor.{u}).Full where
  map_surjective Φ := exists_lift Φ

/-! ### Essential surjectivity: the spectrum of a measurable locale -/

/-- Every measurable locale is the algebra `M/N` of `TM(S)` for a hyperstonean space `S`
(Propositions 2.72 and 2.73). -/
lemma exists_hstonean (L : MLoc.{u}) :
    ∃ S : HStonean.{u}, Nonempty (L.carrier ≃o MmodN (TM S.toTop)) := by
  obtain ⟨e₂, ι₂, -⟩ := proposition_2_73.{u}
  obtain ⟨e₁, ⟨η⟩⟩ := proposition_2_72.{u}
  let L' : HStoneanLoc.{u} := e₂.inverse.obj L
  let S : HStonean.{u} := e₁.inverse.obj L'
  have : CompactSpace S.toTop := hstonean_compact S
  have : T2Space S.toTop := hstonean_t2 S
  have : ExtremallyDisconnected S.toTop := hstonean_extremallyDisconnected S
  -- the order isomorphisms extracted from the equivalences
  let i1 : L.carrier ≃o (e₂.functor.obj L').carrier := mlocOrderIso (e₂.counitIso.app L)
  let i2 : (e₂.functor.obj L').carrier ≃o {a : L'.carrier // IsCompactElement a} := ι₂ L'
  let i3 : L'.carrier ≃o (e₁.functor.obj S).carrier :=
    localeOrderIso (P := (e₁.functor.obj S).carrier) (Q := L'.carrier)
      (HStoneanLoc.toLocale.mapIso (e₁.counitIso.app L'))
  let i4 : Opens S.toTop ≃o (e₁.functor.obj S).carrier :=
    localeOrderIso (P := (e₁.functor.obj S).carrier) (Q := Opens S.toTop) (η.app S)
  let ω : L'.carrier ≃o Opens S.toTop := i3.trans i4.symm
  have hclopen : ∀ x : {a : L'.carrier // IsCompactElement a}, IsClopen ((ω x.1 : Opens S.toTop) : Set S.toTop) :=
    fun x => (isCompactElement_iff_isClopen _).1 (isCompactElement_orderIso ω x.2)
  refine ⟨S, ⟨OrderIso.ofSurjective (OrderEmbedding.ofMapLEIff
    (fun b => MmodN.mk ((ω (i2 (i1 b)).1 : Opens S.toTop) : Set S.toTop)
      (tm_meas_of_isOpen (ω (i2 (i1 b)).1).isOpen)) ?_) ?_⟩⟩
  · intro a b
    rw [mk_le_mk_clopen (hclopen _) (hclopen _), SetLike.coe_subset_coe, ω.le_iff_le,
      Subtype.coe_le_coe, i2.le_iff_le, i1.le_iff_le]
  · intro q
    obtain ⟨K, hK, rfl⟩ := exists_clopen_rep q
    have hk : IsCompactElement (ω.symm ⟨K, hK.isOpen⟩) :=
      isCompactElement_orderIso ω.symm ((isCompactElement_iff_isClopen _).2 hK)
    refine ⟨i1.symm (i2.symm ⟨ω.symm ⟨K, hK.isOpen⟩, hk⟩), ?_⟩
    apply mk_congr
    show ((ω (i2 (i1 (i1.symm (i2.symm ⟨ω.symm ⟨K, hK.isOpen⟩, hk⟩)))).1 : Opens S.toTop) :
      Set S.toTop) = K
    rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
    rfl

instance mlFunctor_essSurj : (mlFunctor.{u}).EssSurj where
  mem_essImage L := by
    obtain ⟨S, ⟨e⟩⟩ := exists_hstonean L
    exact ⟨⟨EMS.of S.toTop (TM S.toTop), proposition_5_4.1 S⟩,
      ⟨mlocIsoMk (A := mlObj ⟨EMS.of S.toTop (TM S.toTop), proposition_5_4.1 S⟩) (B := L)
        (e.trans (κ ⟨EMS.of S.toTop (TM S.toTop), proposition_5_4.1 S⟩))⟩⟩

instance mlFunctor_isEquivalence : (mlFunctor.{u}).IsEquivalence where

end GelfandVNA.Duality.T519

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
  GelfandVNA.Duality.T519 in
/-- Theorem 5.19, p. 45: `ML : CSLEMS → MLoc` is an equivalence of categories. -/
theorem solution.{u} :
    ∃ e : CSLEMS.{u} ≌ MLoc.{u},
      ∃ ι : ∀ A : CSLEMS.{u}, (e.functor.obj A).carrier ≃o MmodN A.obj.E,
        ∀ {A B : CSLEMS.{u}} (f : A ⟶ B) (b : (e.functor.obj B).carrier),
          ι A (MLoc.frameHom (e.functor.map f) b) = pullHom f.hom (ι B b) := by
  refine ⟨mlFunctor.asEquivalence, fun A => (κ A).symm, ?_⟩
  intro A B f b
  show (κ A).symm (κ A (pullHom f.hom ((κ B).symm b))) = pullHom f.hom ((κ B).symm b)
  exact (κ A).symm_apply_apply _
