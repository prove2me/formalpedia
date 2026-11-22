-- Prove2me | solution 1 for CGSpace.exponential_law
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:05:52.0887+00:00
-- url     : https://prove2.me/submissions/94919f2c-6111-4684-a6c0-621fab4553de

import Definitions.Def_CGSpace_FunctionSpace

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGSpace

namespace Sol_CGSpace_exponential_law

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

/-- A map out of `k(A)` is continuous as soon as its composites with all continuous maps from
compact Hausdorff spaces to `A` are continuous. -/
theorem kspace_continuous_dom {A : Type u} [TopologicalSpace A] {W : Type*} [TopologicalSpace W]
    (h : KSpace A → W)
    (hh : ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (g : K → A),
      Continuous g → Continuous (fun s => h (KSpace.mk (g s)))) : Continuous h := by
  refine @continuous_from_compactlyGenerated A W _ _ h ?_
  intro S g
  exact hh S g g.continuous

/-- A continuous map from a compactly generated space to `A` is continuous as a map to `k(A)`. -/
theorem kspace_continuous_mk_comp {T A : Type u} [TopologicalSpace T] [CompactlyGeneratedSpace T]
    [TopologicalSpace A] {φ : T → A} (hφ : Continuous φ) :
    Continuous (fun t => KSpace.mk (φ t)) :=
  continuous_kTop (W := A) hφ

/-- The identity `k(A) → A` is continuous. -/
theorem kspace_continuous_symm {A : Type u} [TopologicalSpace A] :
    Continuous (fun p : KSpace A => KSpace.mk.symm p) :=
  continuous_id_iff_le.2 (compactlyGenerated_le A)

/-! ### Continuity into the compact-open topology defined by test maps -/

/-- If `(t, s) ↦ φ t (g s)` is continuous on `T × K` for every test map `g : K → A`, then `φ` is
continuous for the compact-open topology defined by test maps (tube lemma). -/
theorem continuous_probe_of {T : Type*} [TopologicalSpace T] {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (φ : T → C(A, B))
    (h : ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (g : K → A),
      Continuous g → Continuous (fun p : T × K => φ p.1 (g p.2))) :
    Continuous[inferInstance, probeCompactOpen A B] φ := by
  refine continuous_generateFrom_iff.2 ?_
  rintro N ⟨S, g, U, hU, rfl⟩
  have hF : Continuous (fun p : T × S => φ p.1 (g p.2)) := h S g g.continuous
  have hc : IsClosed ((fun p : T × S => φ p.1 (g p.2)) ⁻¹' Uᶜ) :=
    hU.isClosed_compl.preimage hF
  have hcl : IsClosed (Prod.fst '' ((fun p : T × S => φ p.1 (g p.2)) ⁻¹' Uᶜ)) :=
    isClosedMap_fst_of_compactSpace _ hc
  have hEq : φ ⁻¹' {f : C(A, B) | ∀ t : S, f (g t) ∈ U} =
      (Prod.fst '' ((fun p : T × S => φ p.1 (g p.2)) ⁻¹' Uᶜ))ᶜ := by
    ext t
    constructor
    · rintro ht ⟨⟨t', s⟩, hp, rfl⟩
      exact hp (ht s)
    · intro ht s
      by_contra hs
      exact ht ⟨(t, s), hs, rfl⟩
  rw [hEq]
  exact hcl.isOpen_compl

/-- If `φ` is continuous for the compact-open topology defined by test maps, then
`(t, s) ↦ φ t (g s)` is continuous on `T × K` for every test map `g : K → A`. -/
theorem continuous_of_probe {T : Type*} [TopologicalSpace T] {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (φ : T → C(A, B))
    (hφ : Continuous[inferInstance, probeCompactOpen A B] φ)
    (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (g : K → A)
    (hg : Continuous g) : Continuous (fun p : T × K => φ p.1 (g p.2)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, s₀⟩
  rw [ContinuousAt, tendsto_nhds]
  intro U hU hmem
  -- a neighbourhood of `s₀` on which the single map `φ t₀ ∘ g` takes values in `U`
  have hV : (fun s : K => φ t₀ (g s)) ⁻¹' U ∈ 𝓝 s₀ :=
    ((φ t₀).continuous.comp hg).continuousAt.preimage_mem_nhds (hU.mem_nhds hmem)
  -- shrink it to a compact neighbourhood `L`
  obtain ⟨L, hL_nhds, hL_sub, hL_compact⟩ := local_compact_nhds hV
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL_compact
  -- the sub-basic open set `N(g|L, U)`
  have hN : IsOpen[probeCompactOpen A B] {f : C(A, B) | ∀ s : L, f (g s) ∈ U} :=
    TopologicalSpace.isOpen_generateFrom_of_mem
      ⟨CompHaus.of L, ⟨fun s : L => g s, hg.comp continuous_subtype_val⟩, U, hU, rfl⟩
  have h1 : φ ⁻¹' {f : C(A, B) | ∀ s : L, f (g s) ∈ U} ∈ 𝓝 t₀ :=
    (continuous_def.mp hφ _ hN).mem_nhds (fun s => hL_sub s.2)
  have h2 : (φ ⁻¹' {f : C(A, B) | ∀ s : L, f (g s) ∈ U}) ×ˢ L ∈ 𝓝 (t₀, s₀) :=
    prod_mem_nhds h1 hL_nhds
  filter_upwards [h2] with p hp
  exact hp.1 ⟨p.2, hp.2⟩

/-! ### Continuity of maps into and out of `Cont_k(A, B)` -/

/-- If `ψ : T → Cont_k(A, B)` is continuous, then `(t, s) ↦ ψ t (g s)` is continuous on `T × K`
for every test map `g : K → A`. -/
theorem contK_continuous_apply {T : Type*} [TopologicalSpace T] {A B : Type u}
    [TopologicalSpace A] [TopologicalSpace B] {ψ : T → ContK A B} (hψ : Continuous ψ)
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K] {g : K → A}
    (hg : Continuous g) :
    Continuous (fun p : T × K => ContK.toContinuousMap (ψ p.1) (g p.2)) := by
  have h' : Continuous[inferInstance, probeCompactOpen A B]
      (fun t : T => ContK.toContinuousMap (ψ t)) :=
    continuous_le_rng (compactlyGenerated_le (t := probeCompactOpen A B) C(A, B)) hψ
  exact continuous_of_probe _ h' K g hg

/-- If `T` is compactly generated and `(t, s) ↦ ψ t (g s)` is continuous on `T × K` for every test
map `g : K → A`, then `ψ : T → Cont_k(A, B)` is continuous. -/
theorem contK_continuous_of_apply {T : Type u} [TopologicalSpace T] [CompactlyGeneratedSpace T]
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (ψ : T → ContK A B)
    (h : ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (g : K → A),
      Continuous g → Continuous (fun p : T × K => ContK.toContinuousMap (ψ p.1) (g p.2))) :
    Continuous ψ := by
  have h1 : Continuous[inferInstance, probeCompactOpen A B]
      (fun t : T => ContK.toContinuousMap (ψ t)) :=
    continuous_probe_of _ h
  exact continuous_kTop (t := probeCompactOpen A B) h1

/-- A map out of `Cont_k(A, B)` is continuous as soon as its composites with all continuous maps
from compact Hausdorff spaces to `Cont_k(A, B)` are continuous. -/
theorem contK_continuous_dom {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {W : Type*} [TopologicalSpace W] (h : ContK A B → W)
    (hh : ∀ (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T] (ψ : T → ContK A B),
      Continuous ψ → Continuous (fun t => h (ψ t))) : Continuous h := by
  refine @continuous_from_compactlyGenerated C(A, B) W (probeCompactOpen A B) _ h ?_
  rintro S ⟨g, hg⟩
  exact hh S g (continuous_kTop_of_compact (t := probeCompactOpen A B) hg)

/-! ### Currying -/

section Curry

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A continuous map on the `k`-product is continuous in the second variable. -/
theorem curry_continuous₁ [CompactlyGeneratedSpace Y] (f : C(KSpace (X × Y), Z)) (x : X) :
    Continuous (fun y : Y => f (KSpace.mk (x, y))) :=
  f.continuous.comp
    (kspace_continuous_mk_comp (φ := fun y : Y => (x, y)) (continuous_const.prodMk continuous_id))

/-- The curried map `x ↦ f(x, ·)` is continuous into `Cont_k(Y, Z)`. -/
theorem curry_continuous₂ [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y]
    (f : C(KSpace (X × Y), Z)) :
    Continuous (fun x : X =>
      (ContK.toContinuousMap.symm ⟨fun y : Y => f (KSpace.mk (x, y)), curry_continuous₁ f x⟩ :
        ContK Y Z)) := by
  refine continuous_from_compactlyGeneratedSpace _ ?_
  intro T _ _ _ h hh
  refine contK_continuous_of_apply _ ?_
  intro S _ _ _ g hg
  have hpair : Continuous (fun p : T × S => (h p.1, g p.2)) :=
    (hh.comp continuous_fst).prodMk (hg.comp continuous_snd)
  exact f.continuous.comp (kspace_continuous_mk_comp hpair)

/-- The uncurried map `(x, y) ↦ φ x y` is continuous on the `k`-product. -/
theorem uncurry_continuous (φ : C(X, ContK Y Z)) :
    Continuous (fun p : KSpace (X × Y) =>
      ContK.toContinuousMap (φ (KSpace.mk.symm p).1) (KSpace.mk.symm p).2) := by
  refine kspace_continuous_dom _ ?_
  intro S _ _ _ g hg
  have h1 : Continuous (fun s : S => φ (g s).1) := φ.continuous.comp (continuous_fst.comp hg)
  have h2 : Continuous (fun p : S × S => ContK.toContinuousMap (φ (g p.1).1) (g p.2).2) :=
    contK_continuous_apply h1 (g := fun s : S => (g s).2) (continuous_snd.comp hg)
  exact h2.comp (continuous_id.prodMk continuous_id)

/-- The currying bijection `θ(f)(x)(y) = f(x, y)`. -/
def curryEquiv [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] :
    ContK (KSpace (X × Y)) Z ≃ ContK X (ContK Y Z) where
  toFun f := ContK.toContinuousMap.symm
    ⟨fun x : X => (ContK.toContinuousMap.symm
        ⟨fun y : Y => ContK.toContinuousMap f (KSpace.mk (x, y)),
          curry_continuous₁ (ContK.toContinuousMap f) x⟩ : ContK Y Z),
      curry_continuous₂ (ContK.toContinuousMap f)⟩
  invFun φ := ContK.toContinuousMap.symm
    ⟨fun p : KSpace (X × Y) =>
        ContK.toContinuousMap (ContK.toContinuousMap φ (KSpace.mk.symm p).1) (KSpace.mk.symm p).2,
      uncurry_continuous (ContK.toContinuousMap φ)⟩
  left_inv f := by
    show (_ : C(KSpace (X × Y), Z)) = _
    exact ContinuousMap.ext fun p => rfl
  right_inv φ := by
    show (_ : C(X, ContK Y Z)) = _
    refine ContinuousMap.ext fun x => ?_
    show (_ : C(Y, Z)) = _
    exact ContinuousMap.ext fun y => rfl

theorem curryEquiv_apply [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y]
    (f : ContK (KSpace (X × Y)) Z) (x : X) (y : Y) :
    ContK.toContinuousMap (ContK.toContinuousMap (curryEquiv f) x) y =
      ContK.toContinuousMap f (KSpace.mk (x, y)) := rfl

theorem curryEquiv_symm_apply [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y]
    (φ : ContK X (ContK Y Z)) (p : KSpace (X × Y)) :
    ContK.toContinuousMap (curryEquiv.symm φ) p =
      ContK.toContinuousMap (ContK.toContinuousMap φ (KSpace.mk.symm p).1) (KSpace.mk.symm p).2 :=
  rfl

/-- Currying is continuous. -/
theorem continuous_curryEquiv [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] :
    Continuous (curryEquiv : ContK (KSpace (X × Y)) Z ≃ ContK X (ContK Y Z)) := by
  refine contK_continuous_dom _ ?_
  intro T _ _ _ ψ hψ
  refine contK_continuous_of_apply _ ?_
  intro S₁ _ _ _ g₁ hg₁
  refine contK_continuous_of_apply
    (fun p : T × S₁ => ContK.toContinuousMap (curryEquiv (ψ p.1)) (g₁ p.2)) ?_
  intro S₂ _ _ _ g₂ hg₂
  have hpair : Continuous (fun q : S₁ × S₂ => (g₁ q.1, g₂ q.2)) :=
    (hg₁.comp continuous_fst).prodMk (hg₂.comp continuous_snd)
  have h : Continuous (fun p : T × (S₁ × S₂) =>
      ContK.toContinuousMap (ψ p.1) (KSpace.mk (g₁ p.2.1, g₂ p.2.2))) :=
    contK_continuous_apply hψ (kspace_continuous_mk_comp hpair)
  have hassoc : Continuous (fun r : (T × S₁) × S₂ => (r.1.1, (r.1.2, r.2))) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact h.comp hassoc

/-- Uncurrying is continuous. -/
theorem continuous_curryEquiv_symm [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] :
    Continuous (curryEquiv : ContK (KSpace (X × Y)) Z ≃ ContK X (ContK Y Z)).symm := by
  refine contK_continuous_dom _ ?_
  intro T _ _ _ ψ hψ
  refine contK_continuous_of_apply _ ?_
  intro S _ _ _ g hg
  have hg' : Continuous (fun s : S => KSpace.mk.symm (g s)) := kspace_continuous_symm.comp hg
  have h1 : Continuous (fun p : T × S =>
      ContK.toContinuousMap (ψ p.1) (KSpace.mk.symm (g p.2)).1) :=
    contK_continuous_apply hψ (g := fun s : S => (KSpace.mk.symm (g s)).1)
      (continuous_fst.comp hg')
  have h2 : Continuous (fun r : (T × S) × S =>
      ContK.toContinuousMap (ContK.toContinuousMap (ψ r.1.1) (KSpace.mk.symm (g r.1.2)).1)
        (KSpace.mk.symm (g r.2)).2) :=
    contK_continuous_apply h1 (g := fun s : S => (KSpace.mk.symm (g s)).2)
      (continuous_snd.comp hg')
  have hd : Continuous (fun p : T × S => ((p.1, p.2), p.2)) :=
    (continuous_fst.prodMk continuous_snd).prodMk continuous_snd
  exact h2.comp hd

end Curry

end Sol_CGSpace_exponential_law

open Sol_CGSpace_exponential_law

theorem solution
    (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] [CompactlyGeneratedSpace Z] :
    ∃ e : ContK (KSpace (X × Y)) Z ≃ₜ ContK X (ContK Y Z),
      ∀ (f : ContK (KSpace (X × Y)) Z) (x : X) (y : Y),
        ContK.toContinuousMap (ContK.toContinuousMap (e f) x) y =
          ContK.toContinuousMap f (KSpace.mk (x, y)) :=
  ⟨⟨curryEquiv, continuous_curryEquiv, continuous_curryEquiv_symm⟩, fun _ _ _ => rfl⟩
