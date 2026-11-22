-- Prove2me | solution 1 for CGWH.cartesianClosed
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:28:30.069483+00:00
-- url     : https://prove2.me/submissions/9c7daebf-9f7a-4b52-9be8-10c7c3f297df

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGSpace_exponential_law
import Theorems.Thm_CGWH_weaklyHausdorffSpace_contK

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGWH CGSpace

namespace Sol_CGWH_cartesianClosed

/-! ### A criterion for `Y ⨯ -` to be a left adjoint -/

section Abstract

open Limits

universe v w

variable {C : Type w} [Category.{v} C]

/-- Let `Y` be an object of a category with binary products. Suppose that for every `X` a product
`P X` of `Y` and `X` is given, with projections `pY X`, `pX X`, together with bijections
`e X Z : (P X ⟶ Z) ≃ (X ⟶ H Z)` which are natural in `X`. Then `Y ⨯ -` is a left adjoint. -/
theorem isLeftAdjoint_prod_of_curry [HasBinaryProducts C] (Y : C)
    (P : C → C) (pY : ∀ X, P X ⟶ Y) (pX : ∀ X, P X ⟶ X)
    (hP : ∀ X, IsLimit (BinaryFan.mk (pY X) (pX X)))
    (H : C → C) (e : ∀ X Z, (P X ⟶ Z) ≃ (X ⟶ H Z))
    (he : ∀ {X' X Z : C} (f : X' ⟶ X) (m : P X' ⟶ P X), m ≫ pY X = pY X' →
      m ≫ pX X = pX X' ≫ f → ∀ k : P X ⟶ Z, e X' Z (m ≫ k) = f ≫ e X Z k) :
    (prod.functor.obj Y).IsLeftAdjoint := by
  let i : ∀ X, (Y ⨯ X) ≅ P X := fun X =>
    (limit.isLimit (pair Y X)).conePointUniqueUpToIso (hP X)
  have hi₁ : ∀ X, (i X).hom ≫ pY X = prod.fst := fun X =>
    IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (pair Y X)) (hP X)
      (Discrete.mk WalkingPair.left)
  have hi₂ : ∀ X, (i X).hom ≫ pX X = prod.snd := fun X =>
    IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (pair Y X)) (hP X)
      (Discrete.mk WalkingPair.right)
  have hi₁' : ∀ X, (i X).inv ≫ prod.fst = pY X := fun X => by
    rw [Iso.inv_comp_eq, hi₁]
  have hi₂' : ∀ X, (i X).inv ≫ prod.snd = pX X := fun X => by
    rw [Iso.inv_comp_eq, hi₂]
  have key : ∀ {X' X Z : C} (f : X' ⟶ X) (g : (Y ⨯ X) ⟶ Z),
      e X' Z ((i X').inv ≫ (prod.map (𝟙 Y) f ≫ g) ≫ 𝟙 Z) =
        f ≫ e X Z ((i X).inv ≫ g ≫ 𝟙 Z) := by
    intro X' X Z f g
    have h₁ : ((i X').inv ≫ prod.map (𝟙 Y) f ≫ (i X).hom) ≫ pY X = pY X' := by
      rw [Category.assoc, Category.assoc, hi₁, prod.map_fst, Category.comp_id, hi₁']
    have h₂ : ((i X').inv ≫ prod.map (𝟙 Y) f ≫ (i X).hom) ≫ pX X = pX X' ≫ f := by
      rw [Category.assoc, Category.assoc, hi₂, prod.map_snd, ← Category.assoc, hi₂']
    have hm := he f ((i X').inv ≫ prod.map (𝟙 Y) f ≫ (i X).hom) h₁ h₂ ((i X).inv ≫ g)
    rw [Category.comp_id, Category.comp_id, ← hm]
    congr 1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  let E : ∀ X Z, ((prod.functor.obj Y).obj X ⟶ Z) ≃ (X ⟶ H Z) := fun X Z =>
    ((i X).homCongr (Iso.refl Z)).trans (e X Z)
  refine (Adjunction.adjunctionOfEquivRight E ?_).isLeftAdjoint
  intro X' X Z f g
  exact key f g

end Abstract

/-! ### The `k`-ification -/

/-- The `k`-ification of a topology is finer than the topology. -/
theorem compactlyGenerated_le (W : Type u) [t : TopologicalSpace W] :
    compactlyGenerated.{u} W ≤ t := by
  simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
    Sigma.forall]
  exact fun S f ↦ f.2

/-- A continuous map from a compact Hausdorff space (of the universe of `W`) to `W` is continuous
for the `k`-ified topology of `W`. -/
theorem continuous_kTop_of_compact {K W : Type u} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [t : TopologicalSpace W] {φ : K → W} (hφ : Continuous φ) :
    Continuous[inferInstance, compactlyGenerated.{u} W] φ := by
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, W)), i.fst) → W := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  suffices h : ∀ (i : (T : CompHaus.{u}) × C(T, W)),
      Continuous[inferInstance, compactlyGenerated.{u} W] (fun (a : i.fst) ↦ f ⟨i, a⟩) from
    h ⟨CompHaus.of K, ⟨φ, hφ⟩⟩
  rw [← @continuous_sigma_iff]
  apply continuous_coinduced_rng

/-- A continuous map from a compactly generated space to `W` is continuous for the `k`-ified
topology of `W`. -/
theorem continuous_kTop {T W : Type u} [TopologicalSpace T] [CompactlyGeneratedSpace T]
    [t : TopologicalSpace W] {φ : T → W} (hφ : Continuous φ) :
    Continuous[inferInstance, compactlyGenerated.{u} W] φ :=
  @continuous_from_compactlyGeneratedSpace T W _ (compactlyGenerated.{u} W) _ φ
    (fun _ _ _ _ _ hg => continuous_kTop_of_compact (hφ.comp hg))

/-- The `k`-ification of a topological space is compactly generated. -/
theorem compactlyGeneratedSpace_kTop (W : Type u) [t : TopologicalSpace W] :
    @CompactlyGeneratedSpace W (compactlyGenerated.{u} W) := by
  refine @uCompactlyGeneratedSpace_of_continuous_maps W (compactlyGenerated.{u} W)
    fun {Y} tY f h => ?_
  refine @continuous_from_compactlyGenerated W Y t tY f fun S g => ?_
  exact h S (@ContinuousMap.mk _ _ _ (compactlyGenerated.{u} W) g
    (continuous_kTop_of_compact (t := t) g.continuous))

instance instKSpace (A : Type u) [TopologicalSpace A] : CompactlyGeneratedSpace (KSpace A) :=
  compactlyGeneratedSpace_kTop A

instance instContK (A B : Type u) [TopologicalSpace A] [TopologicalSpace B] :
    CompactlyGeneratedSpace (ContK A B) :=
  @compactlyGeneratedSpace_kTop C(A, B) (probeCompactOpen A B)

/-- A continuous map from a compactly generated space to `A` is continuous as a map to `k(A)`. -/
theorem kspace_continuous_mk_comp {T A : Type u} [TopologicalSpace T] [CompactlyGeneratedSpace T]
    [TopologicalSpace A] {φ : T → A} (hφ : Continuous φ) :
    Continuous (fun t => KSpace.mk (φ t)) :=
  continuous_kTop (W := A) hφ

/-- The identity `k(A) → A` is continuous. -/
theorem kspace_continuous_symm {A : Type u} [TopologicalSpace A] :
    Continuous (fun p : KSpace A => KSpace.mk.symm p) :=
  continuous_id_iff_le.2 (compactlyGenerated_le A)

/-- A subset of `Z` is closed for the `k`-ification of the topology of `Z` iff its preimage under
every continuous map from a compact Hausdorff space is closed. -/
theorem isClosed_compactlyGenerated_iff {Z : Type u} [t : TopologicalSpace Z] (s : Set Z) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} Z] s ↔
      ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (f : K → Z),
        Continuous f → IsClosed (f ⁻¹' s) := by
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  constructor
  · intro h K _ _ _ f hf
    exact h ⟨CompHaus.of K, ⟨f, hf⟩⟩
  · rintro h ⟨S, f⟩
    exact h S f f.continuous

/-! ### Weakly Hausdorff spaces -/

/-- In a weakly Hausdorff space the image of a closed subset of a compact Hausdorff space under a
continuous map is closed. -/
theorem isClosed_image_of_weaklyHausdorff {Y : Type u} [TopologicalSpace Y]
    [WeaklyHausdorffSpace Y] {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {f : K → Y} (hf : Continuous f) {C : Set K} (hC : IsClosed C) : IsClosed (f '' C) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  have h := WeaklyHausdorffSpace.isClosed_range (X := Y) C (f ∘ (Subtype.val : C → K))
    (hf.comp continuous_subtype_val)
  rwa [Set.range_comp, Subtype.range_coe] at h

/-- Points of a weakly Hausdorff space are closed. -/
theorem isClosed_singleton_of_weaklyHausdorff {Y : Type u} [TopologicalSpace Y]
    [WeaklyHausdorffSpace Y] (y : Y) : IsClosed ({y} : Set Y) := by
  have h := WeaklyHausdorffSpace.isClosed_range (X := Y) PUnit.{u + 1} (fun _ => y)
    continuous_const
  rwa [Set.range_const] at h

/-- The coincidence set of two continuous maps from a compact Hausdorff space to a weakly
Hausdorff space is closed. -/
theorem isClosed_setOf_eq_of_compact {Y : Type u} [TopologicalSpace Y] [WeaklyHausdorffSpace Y]
    {T : Type u} [TopologicalSpace T] [CompactSpace T] [T2Space T] {a b : T → Y}
    (ha : Continuous a) (hb : Continuous b) : IsClosed {t : T | a t = b t} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro t₀ ht₀
  have hne : a t₀ ≠ b t₀ := ht₀
  -- the open neighbourhood `{t | a t ≠ b t₀}` of `t₀`
  have hU : {t : T | a t ∈ ({b t₀} : Set Y)ᶜ} ∈ 𝓝 t₀ :=
    ((isClosed_singleton_of_weaklyHausdorff (b t₀)).isOpen_compl.preimage ha).mem_nhds hne
  -- a closed neighbourhood `L` of `t₀` inside it
  obtain ⟨L, hL, hLc, hLU⟩ := exists_mem_nhds_isClosed_subset hU
  have hAL : IsClosed (a '' L) := isClosed_image_of_weaklyHausdorff ha hLc
  have hb₀ : b t₀ ∉ a '' L := by
    rintro ⟨t, htL, ht⟩
    exact hLU htL ht
  have hV : {t : T | b t ∈ (a '' L)ᶜ} ∈ 𝓝 t₀ :=
    (hAL.isOpen_compl.preimage hb).mem_nhds hb₀
  filter_upwards [hL, hV] with t htL htV
  intro h
  have h' : a t = b t := h
  exact htV (h' ▸ ⟨t, htL, rfl⟩)

/-- The one-point space is weakly Hausdorff. -/
theorem weaklyHausdorffSpace_punit : WeaklyHausdorffSpace PUnit.{u + 1} :=
  ⟨fun _ _ _ _ _ _ => isClosed_discrete _⟩

/-- The `k`-ified product `k(X × Y)` of two weakly Hausdorff spaces is weakly Hausdorff. -/
theorem weaklyHausdorffSpace_kProd (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [WeaklyHausdorffSpace X] [WeaklyHausdorffSpace Y] : WeaklyHausdorffSpace (KSpace (X × Y)) := by
  refine ⟨fun K _ _ _ f hf => ?_⟩
  -- `f` is continuous for the product topology
  let f' : K → X × Y := fun k => KSpace.mk.symm (f k)
  have hf' : Continuous f' := kspace_continuous_symm.comp hf
  change IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × Y)] (Set.range f')
  rw [isClosed_compactlyGenerated_iff]
  intro S _ _ _ g hg
  -- the coincidence set of `g` and `f'` in `S × K`
  have hE : IsClosed {p : S × K | g p.1 = f' p.2} := by
    have hEq : {p : S × K | g p.1 = f' p.2} =
        {p : S × K | (g p.1).1 = (f' p.2).1} ∩ {p : S × K | (g p.1).2 = (f' p.2).2} := by
      ext p
      exact Prod.ext_iff
    rw [hEq]
    exact (isClosed_setOf_eq_of_compact
        (a := fun p : S × K => (g p.1).1) (b := fun p : S × K => (f' p.2).1)
        (continuous_fst.comp (hg.comp continuous_fst))
        (continuous_fst.comp (hf'.comp continuous_snd))).inter
      (isClosed_setOf_eq_of_compact
        (a := fun p : S × K => (g p.1).2) (b := fun p : S × K => (f' p.2).2)
        (continuous_snd.comp (hg.comp continuous_fst))
        (continuous_snd.comp (hf'.comp continuous_snd)))
  have himg : g ⁻¹' Set.range f' = Prod.fst '' {p : S × K | g p.1 = f' p.2} := by
    ext s
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨(s, k), hk.symm, rfl⟩
    · rintro ⟨⟨s', k⟩, hsk, rfl⟩
      exact ⟨k, hsk.symm⟩
  rw [himg]
  exact (hE.isCompact.image continuous_fst).isClosed

/-! ### Products of compactly generated spaces -/

section Prod

variable (Y X : CompactlyGenerated.{u, u})

/-- The product `k(X × Y)` of two compactly generated spaces. -/
abbrev kProd : CompactlyGenerated.{u, u} := CompactlyGenerated.of (KSpace (X × Y))

/-- The projection `k(X × Y) → Y`. -/
def kSnd : kProd Y X ⟶ Y :=
  CompactlyGenerated.ofHom
    ⟨fun p => (KSpace.mk.symm p).2, continuous_snd.comp kspace_continuous_symm⟩

/-- The projection `k(X × Y) → X`. -/
def kFst : kProd Y X ⟶ X :=
  CompactlyGenerated.ofHom
    ⟨fun p => (KSpace.mk.symm p).1, continuous_fst.comp kspace_continuous_symm⟩

/-- The pairing of two morphisms. -/
def kLift {T : CompactlyGenerated.{u, u}} (a : T ⟶ Y) (b : T ⟶ X) : T ⟶ kProd Y X :=
  CompactlyGenerated.ofHom ⟨fun t => KSpace.mk (b t, a t),
    kspace_continuous_mk_comp (φ := fun t => (b t, a t))
      (b.hom.hom.continuous.prodMk a.hom.hom.continuous)⟩

theorem kLift_kSnd {T : CompactlyGenerated.{u, u}} (a : T ⟶ Y) (b : T ⟶ X) :
    kLift Y X a b ≫ kSnd Y X = a := by
  ext t; rfl

theorem kLift_kFst {T : CompactlyGenerated.{u, u}} (a : T ⟶ Y) (b : T ⟶ X) :
    kLift Y X a b ≫ kFst Y X = b := by
  ext t; rfl

/-- `k(X × Y)` is a product of `Y` and `X` in the category of compactly generated spaces. -/
def kIsLimit : Limits.IsLimit (Limits.BinaryFan.mk (kSnd Y X) (kFst Y X)) :=
  Limits.BinaryFan.isLimitMk (fun s => kLift Y X s.fst s.snd)
    (fun s => kLift_kSnd Y X s.fst s.snd) (fun s => kLift_kFst Y X s.fst s.snd)
    (fun s m h₁ h₂ => by
      ext t
      have e₁ := congrArg (fun k => k t) h₁
      have e₂ := congrArg (fun k => k t) h₂
      exact Prod.ext e₂ e₁)

/-- The function space object `Cont_k(Y, Z)`. -/
abbrev kHom (Z : CompactlyGenerated.{u, u}) : CompactlyGenerated.{u, u} :=
  CompactlyGenerated.of (ContK Y Z)

/-- Currying on Hom-sets, obtained from the exponential law. -/
noncomputable def curryHom (Z : CompactlyGenerated.{u, u}) :
    (kProd Y X ⟶ Z) ≃ (X ⟶ kHom Y Z) :=
  (ConcreteCategory.homEquiv (X := kProd Y X) (Y := Z)).trans <|
    (ContK.toContinuousMap (X := KSpace (X × Y)) (Y := Z)).symm.trans <|
      (Classical.choose (exponential_law X Y Z)).toEquiv.trans <|
        (ContK.toContinuousMap (X := X) (Y := ContK Y Z)).trans
          (ConcreteCategory.homEquiv (X := X) (Y := kHom Y Z)).symm

theorem curryHom_apply (Z : CompactlyGenerated.{u, u}) (k : kProd Y X ⟶ Z) (x : X) (y : Y) :
    ContK.toContinuousMap (curryHom Y X Z k x) y = k (KSpace.mk (x, y)) :=
  Classical.choose_spec (exponential_law X Y Z)
    (ContK.toContinuousMap.symm (ConcreteCategory.hom k)) x y

/-- Two morphisms into the function space object with the same values are equal. -/
theorem kHom_hom_ext {X Z : CompactlyGenerated.{u, u}} {a b : X ⟶ kHom Y Z}
    (h : ∀ (x : X) (y : Y), ContK.toContinuousMap (a x) y = ContK.toContinuousMap (b x) y) :
    a = b := by
  ext x
  refine ContK.toContinuousMap.injective ?_
  exact ContinuousMap.ext fun y => h x y

/-- Naturality of currying in the first variable: if `m : k(X' × Y) → k(X × Y)` lies over
`f : X' → X` and over the identity of `Y`, then `curry (k ∘ m) = curry k ∘ f`. -/
theorem curryHom_naturality {X' X Z : CompactlyGenerated.{u, u}} (f : X' ⟶ X)
    (m : kProd Y X' ⟶ kProd Y X) (h₁ : m ≫ kSnd Y X = kSnd Y X')
    (h₂ : m ≫ kFst Y X = kFst Y X' ≫ f) (k : kProd Y X ⟶ Z) :
    curryHom Y X' Z (m ≫ k) = f ≫ curryHom Y X Z k := by
  refine kHom_hom_ext Y fun x y => ?_
  rw [curryHom_apply]
  have e₁ : (KSpace.mk.symm (m (KSpace.mk (x, y)))).2 = y :=
    congrArg (fun j => j (KSpace.mk (x, y))) h₁
  have e₂ : (KSpace.mk.symm (m (KSpace.mk (x, y)))).1 = f x :=
    congrArg (fun j => j (KSpace.mk (x, y))) h₂
  have hm : m (KSpace.mk (x, y)) = KSpace.mk (f x, y) := Prod.ext e₂ e₁
  have hk : (m ≫ k) (KSpace.mk (x, y)) = k (KSpace.mk (f x, y)) := congrArg k hm
  rw [hk]
  exact (curryHom_apply Y X Z k (f x) y).symm

end Prod

/-! ### The category of compactly generated weakly Hausdorff spaces -/

section WH

open Limits

/-- The one-point space, as an object of `CGWHCat`. -/
def wPUnit : CGWHCat.{u} :=
  ⟨CompactlyGenerated.of.{u, u} PUnit.{u + 1}, weaklyHausdorffSpace_punit⟩

/-- The one-point space is a terminal object of `CGWHCat`. -/
def isTerminalWPUnit : IsTerminal wPUnit.{u} :=
  IsTerminal.ofUniqueHom
    (fun X => ObjectProperty.homMk
      (CompactlyGenerated.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩))
    (fun X m => by
      apply ObjectProperty.hom_ext
      ext t
      rfl)

variable (Y X : CGWHCat.{u})

/-- The product `k(X × Y)` of two compactly generated weakly Hausdorff spaces is an object of
`CGWHCat`. -/
def wProd : CGWHCat.{u} :=
  ⟨kProd Y.obj X.obj,
    haveI : WeaklyHausdorffSpace X.obj := X.property
    haveI : WeaklyHausdorffSpace Y.obj := Y.property
    weaklyHausdorffSpace_kProd X.obj Y.obj⟩

/-- The projection `k(X × Y) → Y`. -/
def wSnd : wProd Y X ⟶ Y := ObjectProperty.homMk (kSnd Y.obj X.obj)

/-- The projection `k(X × Y) → X`. -/
def wFst : wProd Y X ⟶ X := ObjectProperty.homMk (kFst Y.obj X.obj)

/-- `k(X × Y)` is a product of `Y` and `X` in `CGWHCat`. -/
def wIsLimit : IsLimit (BinaryFan.mk (wSnd Y X) (wFst Y X)) :=
  BinaryFan.isLimitMk
    (fun s => ObjectProperty.homMk (kLift Y.obj X.obj s.fst.hom s.snd.hom))
    (fun s => ObjectProperty.hom_ext _ (kLift_kSnd Y.obj X.obj s.fst.hom s.snd.hom))
    (fun s => ObjectProperty.hom_ext _ (kLift_kFst Y.obj X.obj s.fst.hom s.snd.hom))
    (fun s m h₁ h₂ => by
      apply ObjectProperty.hom_ext
      refine BinaryFan.IsLimit.hom_ext (kIsLimit Y.obj X.obj) ?_ ?_
      · exact (congrArg InducedCategory.Hom.hom h₁).trans
          (kLift_kSnd Y.obj X.obj s.fst.hom s.snd.hom).symm
      · exact (congrArg InducedCategory.Hom.hom h₂).trans
          (kLift_kFst Y.obj X.obj s.fst.hom s.snd.hom).symm)

/-- The function space `Cont_k(Y, Z)` into a compactly generated weakly Hausdorff space is an
object of `CGWHCat`. -/
def wHom (Z : CGWHCat.{u}) : CGWHCat.{u} :=
  ⟨kHom Y.obj Z.obj,
    haveI : WeaklyHausdorffSpace Z.obj := Z.property
    weaklyHausdorffSpace_contK Y.obj Z.obj⟩

/-- Currying on the Hom-sets of `CGWHCat`. -/
noncomputable def wCurry (Z : CGWHCat.{u}) : (wProd Y X ⟶ Z) ≃ (X ⟶ wHom Y Z) :=
  (InducedCategory.homEquiv (X := wProd Y X) (Y := Z)).trans <|
    (curryHom Y.obj X.obj Z.obj).trans (InducedCategory.homEquiv (X := X) (Y := wHom Y Z)).symm

theorem wCurry_naturality {X' X Z : CGWHCat.{u}} (f : X' ⟶ X) (m : wProd Y X' ⟶ wProd Y X)
    (h₁ : m ≫ wSnd Y X = wSnd Y X') (h₂ : m ≫ wFst Y X = wFst Y X' ≫ f) (k : wProd Y X ⟶ Z) :
    wCurry Y X' Z (m ≫ k) = f ≫ wCurry Y X Z k := by
  apply ObjectProperty.hom_ext
  exact curryHom_naturality Y.obj f.hom m.hom (congrArg InducedCategory.Hom.hom h₁)
    (congrArg InducedCategory.Hom.hom h₂) k.hom

/-- The category `CGWHCat` has finite products. -/
theorem hasFiniteProducts : HasFiniteProducts CGWHCat.{u} := by
  have : HasTerminal CGWHCat.{u} := isTerminalWPUnit.hasTerminal
  have : HasBinaryProducts CGWHCat.{u} :=
    @hasBinaryProducts_of_hasLimit_pair _ _ fun {Y X} => ⟨⟨⟨_, wIsLimit Y X⟩⟩⟩
  exact hasFiniteProducts_of_has_binary_and_terminal

/-- In `CGWHCat` the functor `Y × (-)` has a right adjoint. -/
theorem isLeftAdjoint_prod [HasBinaryProducts CGWHCat.{u}] :
    (prod.functor.obj Y).IsLeftAdjoint :=
  isLeftAdjoint_prod_of_curry Y (fun X => wProd Y X) (fun X => wSnd Y X) (fun X => wFst Y X)
    (fun X => wIsLimit Y X) (fun Z => wHom Y Z) (fun X Z => wCurry Y X Z)
    (fun f m h₁ h₂ k => wCurry_naturality Y f m h₁ h₂ k)

end WH

end Sol_CGWH_cartesianClosed

open Sol_CGWH_cartesianClosed

theorem solution :
    ∃ _ : Limits.HasFiniteProducts CGWHCat.{u},
      ∀ Y : CGWHCat.{u}, (Limits.prod.functor.obj Y).IsLeftAdjoint := by
  have h : Limits.HasFiniteProducts CGWHCat.{u} := hasFiniteProducts
  exact ⟨h, fun Y => isLeftAdjoint_prod Y⟩
