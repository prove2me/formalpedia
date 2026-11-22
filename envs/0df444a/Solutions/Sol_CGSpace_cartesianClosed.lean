-- Prove2me | solution 1 for CGSpace.cartesianClosed
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:14:42.265106+00:00
-- url     : https://prove2.me/submissions/74db5adc-0182-49e6-9b80-71960b5d2439

import Mathlib
import Theorems.Thm_CGSpace_exponential_law

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGSpace

namespace Sol_CGSpace_cartesianClosed

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

/-! ### Finite products of compactly generated spaces -/

/-- The one-point space is a terminal object. -/
def isTerminalPUnit : Limits.IsTerminal (CompactlyGenerated.of.{u, u} PUnit.{u + 1}) :=
  Limits.IsTerminal.ofUniqueHom
    (fun X => CompactlyGenerated.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩)
    (fun X m => by ext)

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

end Prod

/-- The category of compactly generated spaces has finite products. -/
theorem hasFiniteProducts : Limits.HasFiniteProducts CompactlyGenerated.{u, u} := by
  have : Limits.HasTerminal CompactlyGenerated.{u, u} := isTerminalPUnit.hasTerminal
  have : Limits.HasBinaryProducts CompactlyGenerated.{u, u} :=
    @Limits.hasBinaryProducts_of_hasLimit_pair _ _ fun {Y X} => ⟨⟨⟨_, kIsLimit Y X⟩⟩⟩
  exact hasFiniteProducts_of_has_binary_and_terminal

/-! ### The adjunction -/

section Adj

variable (Y : CompactlyGenerated.{u, u})

/-- The function space object `Cont_k(Y, Z)`. -/
abbrev kHom (Z : CompactlyGenerated.{u, u}) : CompactlyGenerated.{u, u} :=
  CompactlyGenerated.of (ContK Y Z)

/-- Currying on Hom-sets, obtained from the exponential law. -/
noncomputable def curryHom (X Z : CompactlyGenerated.{u, u}) :
    (kProd Y X ⟶ Z) ≃ (X ⟶ kHom Y Z) :=
  (ConcreteCategory.homEquiv (X := kProd Y X) (Y := Z)).trans <|
    (ContK.toContinuousMap (X := KSpace (X × Y)) (Y := Z)).symm.trans <|
      (Classical.choose (exponential_law X Y Z)).toEquiv.trans <|
        (ContK.toContinuousMap (X := X) (Y := ContK Y Z)).trans
          (ConcreteCategory.homEquiv (X := X) (Y := kHom Y Z)).symm

theorem curryHom_apply (X Z : CompactlyGenerated.{u, u}) (k : kProd Y X ⟶ Z) (x : X) (y : Y) :
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

/-- The map `k(X' × Y) → k(X × Y)` induced by `f : X' → X`. -/
def kMap {X' X : CompactlyGenerated.{u, u}} (f : X' ⟶ X) : kProd Y X' ⟶ kProd Y X :=
  kLift Y X (kSnd Y X') (kFst Y X' ≫ f)

theorem curryHom_naturality {X' X Z : CompactlyGenerated.{u, u}} (f : X' ⟶ X)
    (k : kProd Y X ⟶ Z) : curryHom Y X' Z (kMap Y f ≫ k) = f ≫ curryHom Y X Z k := by
  refine kHom_hom_ext Y fun x y => ?_
  rw [curryHom_apply]
  exact (curryHom_apply Y X Z k (f x) y).symm

variable [Limits.HasBinaryProducts CompactlyGenerated.{u, u}]

/-- The comparison between the chosen product and `k(X × Y)`. -/
noncomputable def prodIso (X : CompactlyGenerated.{u, u}) : (Y ⨯ X) ≅ kProd Y X :=
  (Limits.limit.isLimit (Limits.pair Y X)).conePointUniqueUpToIso (kIsLimit Y X)

theorem prodIso_hom_kSnd (X : CompactlyGenerated.{u, u}) :
    (prodIso Y X).hom ≫ kSnd Y X = Limits.prod.fst :=
  Limits.IsLimit.conePointUniqueUpToIso_hom_comp (Limits.limit.isLimit (Limits.pair Y X))
    (kIsLimit Y X) (Discrete.mk Limits.WalkingPair.left)

theorem prodIso_hom_kFst (X : CompactlyGenerated.{u, u}) :
    (prodIso Y X).hom ≫ kFst Y X = Limits.prod.snd :=
  Limits.IsLimit.conePointUniqueUpToIso_hom_comp (Limits.limit.isLimit (Limits.pair Y X))
    (kIsLimit Y X) (Discrete.mk Limits.WalkingPair.right)

theorem prodIso_naturality {X' X : CompactlyGenerated.{u, u}} (f : X' ⟶ X) :
    Limits.prod.map (𝟙 Y) f ≫ (prodIso Y X).hom = (prodIso Y X').hom ≫ kMap Y f := by
  refine Limits.BinaryFan.IsLimit.hom_ext (kIsLimit Y X) ?_ ?_
  · show (Limits.prod.map (𝟙 Y) f ≫ (prodIso Y X).hom) ≫ kSnd Y X =
      ((prodIso Y X').hom ≫ kMap Y f) ≫ kSnd Y X
    rw [Category.assoc, prodIso_hom_kSnd, Limits.prod.map_fst, Category.comp_id, Category.assoc,
      kMap, kLift_kSnd, prodIso_hom_kSnd]
  · show (Limits.prod.map (𝟙 Y) f ≫ (prodIso Y X).hom) ≫ kFst Y X =
      ((prodIso Y X').hom ≫ kMap Y f) ≫ kFst Y X
    rw [Category.assoc, prodIso_hom_kFst, Limits.prod.map_snd, Category.assoc, kMap, kLift_kFst,
      ← Category.assoc, prodIso_hom_kFst]

theorem curryHom_prodIso_naturality {X' X Z : CompactlyGenerated.{u, u}} (f : X' ⟶ X)
    (g : (Y ⨯ X) ⟶ Z) :
    curryHom Y X' Z ((prodIso Y X').inv ≫ (Limits.prod.map (𝟙 Y) f ≫ g) ≫ 𝟙 Z) =
      f ≫ curryHom Y X Z ((prodIso Y X).inv ≫ g ≫ 𝟙 Z) := by
  have h : (prodIso Y X').inv ≫ Limits.prod.map (𝟙 Y) f = kMap Y f ≫ (prodIso Y X).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact prodIso_naturality Y f
  rw [Category.comp_id, Category.comp_id, ← Category.assoc, h, Category.assoc,
    curryHom_naturality]

/-- The functor `Y × (-)` has a right adjoint. -/
theorem isLeftAdjoint_prod : (Limits.prod.functor.obj Y).IsLeftAdjoint := by
  let e : ∀ X Z : CompactlyGenerated.{u, u},
      ((Limits.prod.functor.obj Y).obj X ⟶ Z) ≃ (X ⟶ kHom Y Z) :=
    fun X Z => ((prodIso Y X).homCongr (Iso.refl Z)).trans (curryHom Y X Z)
  refine (Adjunction.adjunctionOfEquivRight e ?_).isLeftAdjoint
  intro X' X Z f g
  exact curryHom_prodIso_naturality Y f g

end Adj

end Sol_CGSpace_cartesianClosed

open Sol_CGSpace_cartesianClosed

theorem solution :
    ∃ _ : Limits.HasFiniteProducts CompactlyGenerated.{u, u},
      ∀ Y : CompactlyGenerated.{u, u}, (Limits.prod.functor.obj Y).IsLeftAdjoint := by
  have h : Limits.HasFiniteProducts CompactlyGenerated.{u, u} := hasFiniteProducts
  exact ⟨h, fun Y => isLeftAdjoint_prod Y⟩
