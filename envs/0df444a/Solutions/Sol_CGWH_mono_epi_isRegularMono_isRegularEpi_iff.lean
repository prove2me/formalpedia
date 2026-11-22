-- Prove2me | solution 1 for CGWH.mono_epi_isRegularMono_isRegularEpi_iff
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:20:49.902489+00:00
-- url     : https://prove2.me/submissions/8aa1b330-b082-42d3-8750-e6e0e4f3c983

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_weaklyHausdorffSpace_quotient_iff
import Theorems.Thm_CGWH_weaklyHausdorffSpace_iff_isClosed_diagonal

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_mono_epi_isRegularMono_isRegularEpi_iff

open CGWH

/-! ### Topological preliminaries -/

/-- Closed sets of the `k`-ification: a set is `k`-closed iff its preimage under every test map
is closed. -/
theorem isClosed_compactlyGenerated_iff {Y : Type u} [TopologicalSpace Y] (s : Set Y) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} Y] s ↔
      ∀ (K : CompHaus.{u}) (f : C(K, Y)), IsClosed (f ⁻¹' s) := by
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  exact ⟨fun h K f => h ⟨K, f⟩, fun h ⟨K, f⟩ => h K f⟩

/-- The coincidence set of two continuous maps from a compact Hausdorff space to a compactly
generated weakly Hausdorff space is closed. -/
theorem isClosed_setOf_eq_of_compact {K Y : Type u} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [TopologicalSpace Y] [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
    {a b : K → Y} (ha : Continuous a) (hb : Continuous b) : IsClosed {k | a k = b k} := by
  have hΔ : IsClosed[TopologicalSpace.compactlyGenerated.{u} (Y × Y)] (Set.diagonal Y) :=
    (weaklyHausdorffSpace_iff_isClosed_diagonal Y).mp inferInstance
  rw [isClosed_compactlyGenerated_iff] at hΔ
  exact hΔ (CompHaus.of K) ⟨fun k => (a k, b k), ha.prodMk hb⟩

/-- The coincidence set of two continuous maps from a compactly generated space to a compactly
generated weakly Hausdorff space is closed. -/
theorem isClosed_setOf_eq {X Y : Type u} [TopologicalSpace X] [CompactlyGeneratedSpace X]
    [TopologicalSpace Y] [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
    {a b : X → Y} (ha : Continuous a) (hb : Continuous b) : IsClosed {x | a x = b x} := by
  refine CompactlyGeneratedSpace.isClosed' fun K _ _ _ c hc => ?_
  exact isClosed_setOf_eq_of_compact (ha.comp hc) (hb.comp hc)

/-- A subspace of a weakly Hausdorff space is weakly Hausdorff. -/
theorem weaklyHausdorffSpace_subtype {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace X]
    (s : Set X) : WeaklyHausdorffSpace s := by
  refine ⟨fun K _ _ _ f hf => ?_⟩
  have h : IsClosed (Set.range fun k => (f k : X)) :=
    WeaklyHausdorffSpace.isClosed_range K (fun k => (f k : X)) (continuous_subtype_val.comp hf)
  have hrange : Set.range f = Subtype.val ⁻¹' Set.range (fun k => (f k : X)) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
  rw [hrange]
  exact h.preimage continuous_subtype_val

/-- A closed subspace of a compactly generated space is compactly generated. -/
theorem compactlyGeneratedSpace_subtype_of_isClosed {X : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace X] {C : Set X} (hC : IsClosed C) : CompactlyGeneratedSpace C := by
  refine compactlyGeneratedSpace_of_isClosed fun s hs => ?_
  have himg : IsClosed (Subtype.val '' s : Set X) := by
    refine CompactlyGeneratedSpace.isClosed' fun K _ _ _ g hg => ?_
    have hK' : IsClosed (g ⁻¹' C) := hC.preimage hg
    have : CompactSpace (g ⁻¹' C) := isCompact_iff_compactSpace.mp hK'.isCompact
    let g' : g ⁻¹' C → C := fun k => ⟨g k.1, k.2⟩
    have hg' : Continuous g' := (hg.comp continuous_subtype_val).subtype_mk _
    have h1 : IsClosed (g' ⁻¹' s) := hs (g ⁻¹' C) g' hg'
    have h2 : IsClosed (Subtype.val '' (g' ⁻¹' s) : Set K) :=
      hK'.isClosedEmbedding_subtypeVal.isClosedMap _ h1
    have hpre : g ⁻¹' (Subtype.val '' s) = Subtype.val '' (g' ⁻¹' s) := by
      ext k
      constructor
      · rintro ⟨c, hc, hck⟩
        have hkC : g k ∈ C := hck ▸ c.2
        refine ⟨⟨k, hkC⟩, ?_, rfl⟩
        have hceq : g' ⟨k, hkC⟩ = c := Subtype.ext hck.symm
        show g' ⟨k, hkC⟩ ∈ s
        rw [hceq]
        exact hc
      · rintro ⟨k', hk', rfl⟩
        exact ⟨g' k', hk', rfl⟩
    rw [hpre]
    exact h2
  have hs' : s = Subtype.val ⁻¹' (Subtype.val '' s) :=
    (Set.preimage_image_eq _ Subtype.val_injective).symm
  rw [hs']
  exact himg.preimage continuous_subtype_val

/-- A discrete space is weakly Hausdorff. -/
theorem weaklyHausdorffSpace_of_discrete (X : Type u) [TopologicalSpace X] [DiscreteTopology X] :
    WeaklyHausdorffSpace X :=
  ⟨fun _ _ _ _ _ _ => isClosed_discrete _⟩

/-- The quotient of a compactly generated space by the kernel relation of a continuous map to a
compactly generated weakly Hausdorff space is weakly Hausdorff. -/
theorem weaklyHausdorffSpace_quotient_ker {X Y : Type u} [TopologicalSpace X]
    [CompactlyGeneratedSpace X] [TopologicalSpace Y] [CompactlyGeneratedSpace Y]
    [WeaklyHausdorffSpace Y] {f : X → Y} (hf : Continuous f) :
    WeaklyHausdorffSpace (Quotient (Setoid.ker f)) := by
  rw [weaklyHausdorffSpace_quotient_iff, isClosed_compactlyGenerated_iff]
  intro K c
  exact isClosed_setOf_eq_of_compact (K := K) (hf.comp (continuous_fst.comp c.continuous))
    (hf.comp (continuous_snd.comp c.continuous))

/-! ### The double of a space along a closed subset -/

section Double

variable {Y : Type u} [TopologicalSpace Y]

/-- The fold map `Y ⊔ Y → Y`. -/
def fold : Y ⊕ Y → Y := Sum.elim id id

/-- The map `Y ⊔ Y → Bool` recording the summand. -/
def side : Y ⊕ Y → Bool := Sum.elim (fun _ => true) (fun _ => false)

theorem continuous_fold : Continuous (fold : Y ⊕ Y → Y) :=
  continuous_id.sumElim continuous_id

theorem continuous_side : Continuous (side : Y ⊕ Y → Bool) :=
  continuous_const.sumElim continuous_const

/-- The equivalence relation on `Y ⊔ Y` gluing the two copies of `Y` along the subset `Z`. -/
def doubleSetoid (Z : Set Y) : Setoid (Y ⊕ Y) where
  r a b := fold a = fold b ∧ (side a = side b ∨ fold a ∈ Z)
  iseqv :=
    { refl := fun _ => ⟨rfl, Or.inl rfl⟩
      symm := fun {a b} h =>
        ⟨h.1.symm, h.2.elim (fun h' => Or.inl h'.symm) (fun h' => Or.inr (h.1 ▸ h'))⟩
      trans := fun {a b c} h1 h2 => ⟨h1.1.trans h2.1, by
        rcases h1.2 with h | h
        · rcases h2.2 with h' | h'
          · exact Or.inl (h.trans h')
          · exact Or.inr (h1.1 ▸ h')
        · exact Or.inr h⟩ }

/-- The double `Y ∪_Z Y` of a compactly generated weakly Hausdorff space along a closed subset is
weakly Hausdorff. -/
theorem weaklyHausdorffSpace_double [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
    {Z : Set Y} (hZ : IsClosed Z) : WeaklyHausdorffSpace (Quotient (doubleSetoid Z)) := by
  rw [weaklyHausdorffSpace_quotient_iff, isClosed_compactlyGenerated_iff]
  intro K c
  have h1 : Continuous fun k => fold (c k).1 :=
    continuous_fold.comp (continuous_fst.comp c.continuous)
  have h2 : Continuous fun k => fold (c k).2 :=
    continuous_fold.comp (continuous_snd.comp c.continuous)
  have h3 : Continuous fun k => side (c k).1 :=
    continuous_side.comp (continuous_fst.comp c.continuous)
  have h4 : Continuous fun k => side (c k).2 :=
    continuous_side.comp (continuous_snd.comp c.continuous)
  have hset : c ⁻¹' {p : (Y ⊕ Y) × (Y ⊕ Y) | doubleSetoid Z p.1 p.2} =
      {k | fold (c k).1 = fold (c k).2} ∩
        ({k | side (c k).1 = side (c k).2} ∪ (fun k => fold (c k).1) ⁻¹' Z) := by
    ext k
    exact Iff.rfl
  rw [hset]
  exact (isClosed_setOf_eq_of_compact h1 h2).inter ((isClosed_eq h3 h4).union (hZ.preimage h1))

/-- The inclusion of the first copy of `Y` in the double. -/
def dinl (Z : Set Y) : C(Y, Quotient (doubleSetoid Z)) :=
  ⟨fun y => Quotient.mk (doubleSetoid Z) (Sum.inl y), continuous_quotient_mk'.comp continuous_inl⟩

/-- The inclusion of the second copy of `Y` in the double. -/
def dinr (Z : Set Y) : C(Y, Quotient (doubleSetoid Z)) :=
  ⟨fun y => Quotient.mk (doubleSetoid Z) (Sum.inr y), continuous_quotient_mk'.comp continuous_inr⟩

/-- The two inclusions of `Y` in the double along `Z` agree exactly on `Z`. -/
theorem dinl_eq_dinr_iff (Z : Set Y) (y : Y) : dinl Z y = dinr Z y ↔ y ∈ Z := by
  constructor
  · intro h
    have h' : doubleSetoid Z (Sum.inl y) (Sum.inr y) := Quotient.exact h
    rcases h'.2 with h'' | h''
    · exact absurd h'' (by simp [side])
    · exact h''
  · intro h
    exact Quotient.sound ⟨rfl, Or.inr h⟩

end Double

/-! ### Objects and morphisms of `CGWH` -/

instance instWeaklyHausdorffSpaceObj (X : CGWHCat.{u}) : WeaklyHausdorffSpace X.obj := X.property

/-- The object of `CGWH` defined by a compactly generated weakly Hausdorff space. -/
abbrev obj (T : Type u) [TopologicalSpace T] [CompactlyGeneratedSpace T]
    [WeaklyHausdorffSpace T] : CGWHCat.{u} :=
  ⟨CompactlyGenerated.of T, ‹WeaklyHausdorffSpace T›⟩

/-- The morphism of `CGWH` defined by a continuous map. -/
abbrev homOf {X Y : CGWHCat.{u}} (φ : C(X.obj, Y.obj)) : X ⟶ Y :=
  ObjectProperty.homMk (ConcreteCategory.ofHom φ)

theorem hom_ext_fun {X Y : CGWHCat.{u}} {f g : X ⟶ Y}
    (h : ∀ x : X.obj, ConcreteCategory.hom f.hom x = ConcreteCategory.hom g.hom x) : f = g := by
  apply ObjectProperty.hom_ext
  exact ConcreteCategory.hom_ext _ _ h

theorem congr_fun_hom {X Y : CGWHCat.{u}} {f g : X ⟶ Y} (h : f = g) (x : X.obj) :
    ConcreteCategory.hom f.hom x = ConcreteCategory.hom g.hom x := by
  rw [h]

/-! ### Monomorphisms -/

theorem mono_of_injective {X Y : CGWHCat.{u}} (f : X ⟶ Y)
    (hf : Function.Injective (ConcreteCategory.hom f.hom)) : Mono f :=
  ⟨fun _ _ w => hom_ext_fun fun t => hf (congr_fun_hom w t)⟩

theorem injective_of_mono {X Y : CGWHCat.{u}} (f : X ⟶ Y) [Mono f] :
    Function.Injective (ConcreteCategory.hom f.hom) := by
  intro a b hab
  have : WeaklyHausdorffSpace PUnit.{u + 1} := weaklyHausdorffSpace_of_discrete _
  let P : CGWHCat.{u} := obj PUnit.{u + 1}
  let ca : P ⟶ X := homOf ⟨fun _ => a, continuous_const⟩
  let cb : P ⟶ X := homOf ⟨fun _ => b, continuous_const⟩
  have h : ca ≫ f = cb ≫ f := hom_ext_fun fun _ => hab
  exact congr_fun_hom ((cancel_mono f).mp h) PUnit.unit

/-! ### Epimorphisms -/

theorem epi_of_denseRange {X Y : CGWHCat.{u}} (f : X ⟶ Y)
    (hf : DenseRange (ConcreteCategory.hom f.hom)) : Epi f := by
  refine ⟨fun {W} g h w => hom_ext_fun fun y => ?_⟩
  have hE : IsClosed {y : Y.obj | ConcreteCategory.hom g.hom y = ConcreteCategory.hom h.hom y} :=
    isClosed_setOf_eq (ConcreteCategory.hom g.hom).continuous
      (ConcreteCategory.hom h.hom).continuous
  have hsub : Set.range (ConcreteCategory.hom f.hom) ⊆
      {y : Y.obj | ConcreteCategory.hom g.hom y = ConcreteCategory.hom h.hom y} := by
    rintro _ ⟨x, rfl⟩
    exact congr_fun_hom w x
  exact hE.closure_subset_iff.mpr hsub (hf y)

theorem denseRange_of_epi {X Y : CGWHCat.{u}} (f : X ⟶ Y) [Epi f] :
    DenseRange (ConcreteCategory.hom f.hom) := by
  let Z : Set Y.obj := closure (Set.range (ConcreteCategory.hom f.hom))
  have hZ : IsClosed Z := isClosed_closure
  have : WeaklyHausdorffSpace (Quotient (doubleSetoid Z)) := weaklyHausdorffSpace_double hZ
  let D : CGWHCat.{u} := obj (Quotient (doubleSetoid Z))
  let g : Y ⟶ D := homOf (dinl Z)
  let h : Y ⟶ D := homOf (dinr Z)
  have hw : f ≫ g = f ≫ h :=
    hom_ext_fun fun x => (dinl_eq_dinr_iff Z _).mpr (subset_closure ⟨x, rfl⟩)
  have hgh : g = h := (cancel_epi f).mp hw
  intro y
  exact (dinl_eq_dinr_iff Z y).mp (congr_fun_hom hgh y)

/-! ### Regular monomorphisms -/

theorem isClosedEmbedding_of_isRegularMono {X Y : CGWHCat.{u}} (f : X ⟶ Y) [IsRegularMono f] :
    IsClosedEmbedding (ConcreteCategory.hom f.hom) := by
  let l := IsRegularMono.left f
  let r := IsRegularMono.right f
  have hw : f ≫ l = f ≫ r := IsRegularMono.w f
  let E : Set Y.obj := {y | ConcreteCategory.hom l.hom y = ConcreteCategory.hom r.hom y}
  have hE : IsClosed E :=
    isClosed_setOf_eq (ConcreteCategory.hom l.hom).continuous
      (ConcreteCategory.hom r.hom).continuous
  have : CompactlyGeneratedSpace E := compactlyGeneratedSpace_subtype_of_isClosed hE
  have : WeaklyHausdorffSpace E := weaklyHausdorffSpace_subtype E
  let E' : CGWHCat.{u} := obj E
  let i : E' ⟶ Y := homOf ⟨Subtype.val, continuous_subtype_val⟩
  have hi : i ≫ l = i ≫ r := hom_ext_fun fun e => e.2
  let k : E' ⟶ X := IsRegularMono.lift f i hi
  have hk : k ≫ f = i := IsRegularMono.fac f i hi
  have hk' : ∀ e : E, ConcreteCategory.hom f.hom (ConcreteCategory.hom k.hom e) = e.1 :=
    fun e => congr_fun_hom hk e
  have hmem : ∀ x : X.obj, ConcreteCategory.hom f.hom x ∈ E := fun x => congr_fun_hom hw x
  have hinj : Function.Injective (ConcreteCategory.hom f.hom) := injective_of_mono f
  let e : X.obj ≃ₜ E :=
    { toFun := fun x => ⟨ConcreteCategory.hom f.hom x, hmem x⟩
      invFun := ConcreteCategory.hom k.hom
      left_inv := fun x => hinj (hk' _)
      right_inv := fun e => Subtype.ext (hk' e)
      continuous_toFun := (ConcreteCategory.hom f.hom).continuous.subtype_mk _
      continuous_invFun := (ConcreteCategory.hom k.hom).continuous }
  exact hE.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding

theorem isRegularMono_of_isClosedEmbedding {X Y : CGWHCat.{u}} (f : X ⟶ Y)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.hom)) : IsRegularMono f := by
  let Z : Set Y.obj := Set.range (ConcreteCategory.hom f.hom)
  have hZ : IsClosed Z := hf.isClosed_range
  have : WeaklyHausdorffSpace (Quotient (doubleSetoid Z)) := weaklyHausdorffSpace_double hZ
  let D : CGWHCat.{u} := obj (Quotient (doubleSetoid Z))
  let g : Y ⟶ D := homOf (dinl Z)
  let h : Y ⟶ D := homOf (dinr Z)
  have hw : f ≫ g = f ≫ h := hom_ext_fun fun x => (dinl_eq_dinr_iff Z _).mpr ⟨x, rfl⟩
  have key : ∀ (s : Limits.Fork g h) (t : s.pt.obj),
      ∃ x : X.obj, ConcreteCategory.hom f.hom x = ConcreteCategory.hom s.ι.hom t :=
    fun s t => (dinl_eq_dinr_iff Z _).mp (congr_fun_hom s.condition t)
  choose lift hlift using key
  have hcont : ∀ s, Continuous (lift s) := fun s => by
    rw [hf.isEmbedding.continuous_iff]
    have hcomp : (ConcreteCategory.hom f.hom) ∘ lift s = ConcreteCategory.hom s.ι.hom :=
      funext (hlift s)
    rw [hcomp]
    exact (ConcreteCategory.hom s.ι.hom).continuous
  refine ⟨⟨{ Z := D, left := g, right := h, w := hw, isLimit := ?_ }⟩⟩
  refine Limits.Fork.IsLimit.mk _ (fun s => homOf ⟨lift s, hcont s⟩) ?_ ?_
  · intro s
    exact hom_ext_fun fun t => hlift s t
  · intro s m hm
    refine hom_ext_fun fun t => hf.injective ?_
    exact (congr_fun_hom hm t).trans (hlift s t).symm

/-! ### Regular epimorphisms -/

theorem isQuotientMap_of_isRegularEpi {X Y : CGWHCat.{u}} (f : X ⟶ Y) [IsRegularEpi f] :
    IsQuotientMap (ConcreteCategory.hom f.hom) := by
  let φ : C(X.obj, Y.obj) := ConcreteCategory.hom f.hom
  let S : Setoid X.obj := Setoid.ker φ
  have : WeaklyHausdorffSpace (Quotient S) := weaklyHausdorffSpace_quotient_ker φ.continuous
  let Q : CGWHCat.{u} := obj (Quotient S)
  let q : X ⟶ Q := homOf ⟨Quotient.mk S, continuous_quotient_mk'⟩
  let g : Q ⟶ Y := homOf ⟨Quotient.lift φ (fun _ _ h => h), φ.continuous.quotient_lift _⟩
  have hqg : q ≫ g = f := hom_ext_fun fun x => rfl
  have hq : IsRegularEpi.left f ≫ q = IsRegularEpi.right f ≫ q :=
    hom_ext_fun fun z => Quotient.sound (congr_fun_hom (IsRegularEpi.w f) z)
  let d : Y ⟶ Q := IsRegularEpi.desc f q hq
  have hfd : f ≫ d = q := IsRegularEpi.fac f q hq
  have hdg : d ≫ g = 𝟙 Y := by
    rw [← cancel_epi f, ← Category.assoc, hfd, hqg, Category.comp_id]
  have hdg' : ∀ y : Y.obj,
      (ConcreteCategory.hom g.hom) ((ConcreteCategory.hom d.hom) y) = y := fun y =>
    congr_fun_hom hdg y
  have hgq : ∀ x : X.obj, (ConcreteCategory.hom g.hom) (Quotient.mk S x) = φ x := fun _ => rfl
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen fun V =>
    ⟨fun hV => ?_, fun hV => hV.preimage φ.continuous⟩, fun y => ?_⟩
  · have hopen : IsOpen ((ConcreteCategory.hom g.hom) ⁻¹' V) := by
      rw [← (isQuotientMap_quotient_mk' (s := S)).isOpen_preimage]
      exact hV
    have hpre : V = (ConcreteCategory.hom d.hom) ⁻¹' ((ConcreteCategory.hom g.hom) ⁻¹' V) := by
      ext y
      simp only [Set.mem_preimage]
      rw [hdg' y]
    rw [hpre]
    exact hopen.preimage (ConcreteCategory.hom d.hom).continuous
  · obtain ⟨x, hx⟩ := Quotient.exists_rep ((ConcreteCategory.hom d.hom) y)
    refine ⟨x, ?_⟩
    show φ x = y
    rw [← hgq x, hx, hdg' y]

theorem isRegularEpi_of_isQuotientMap {X Y : CGWHCat.{u}} (f : X ⟶ Y)
    (hf : IsQuotientMap (ConcreteCategory.hom f.hom)) : IsRegularEpi f := by
  let φ : C(X.obj, Y.obj) := ConcreteCategory.hom f.hom
  let R : Type u := {p : X.obj × X.obj // φ p.1 = φ p.2}
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have : WeaklyHausdorffSpace R := weaklyHausdorffSpace_of_discrete R
  let W : CGWHCat.{u} := obj R
  let s : W ⟶ X := homOf ⟨fun p : R => p.1.1, continuous_of_discreteTopology⟩
  let t : W ⟶ X := homOf ⟨fun p : R => p.1.2, continuous_of_discreteTopology⟩
  have hw : s ≫ f = t ≫ f := hom_ext_fun fun p => p.2
  let leg : ∀ c : Limits.Cofork s t, C(X.obj, c.pt.obj) := fun c => c.π.hom.hom.hom
  have key : ∀ (c : Limits.Cofork s t), Function.FactorsThrough (leg c) φ := by
    intro c a b hab
    exact congr_fun_hom c.condition (⟨(a, b), hab⟩ : R)
  have hlift : ∀ (c : Limits.Cofork s t) (x : X.obj),
      (hf.lift (leg c) (key c)) (φ x) = leg c x := fun c x =>
    DFunLike.congr_fun (hf.lift_comp (leg c) (key c)) x
  refine ⟨⟨{ W := W, left := s, right := t, w := hw, isColimit := ?_ }⟩⟩
  refine Limits.Cofork.IsColimit.mk _
    (fun c : Limits.Cofork s t => homOf (hf.lift (leg c) (key c))) ?_ ?_
  · intro c
    exact hom_ext_fun fun x => hlift c x
  · intro c m hm
    refine hom_ext_fun fun y => ?_
    obtain ⟨x, rfl⟩ := hf.surjective y
    have h1 : (ConcreteCategory.hom m.hom) (φ x) = leg c x := congr_fun_hom hm x
    exact h1.trans (hlift c x).symm

end Sol_CGWH_mono_epi_isRegularMono_isRegularEpi_iff

open CGWH Sol_CGWH_mono_epi_isRegularMono_isRegularEpi_iff in
theorem solution {X Y : CGWHCat.{u}} (f : X ⟶ Y) :
    (Mono f ↔ Function.Injective (ConcreteCategory.hom f.hom)) ∧
    (Epi f ↔ DenseRange (ConcreteCategory.hom f.hom)) ∧
    (IsRegularMono f ↔ IsClosedEmbedding (ConcreteCategory.hom f.hom)) ∧
    (IsRegularEpi f ↔ IsQuotientMap (ConcreteCategory.hom f.hom)) :=
  ⟨⟨fun _ => injective_of_mono f, mono_of_injective f⟩,
    ⟨fun _ => denseRange_of_epi f, epi_of_denseRange f⟩,
    ⟨fun _ => isClosedEmbedding_of_isRegularMono f, isRegularMono_of_isClosedEmbedding f⟩,
    ⟨fun _ => isQuotientMap_of_isRegularEpi f, isRegularEpi_of_isQuotientMap f⟩⟩
