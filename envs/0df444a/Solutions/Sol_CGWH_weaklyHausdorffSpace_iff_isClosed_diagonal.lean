-- Prove2me | solution 1 for CGWH.weaklyHausdorffSpace_iff_isClosed_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:57:40.327826+00:00
-- url     : https://prove2.me/submissions/8f246c4b-0cac-4c50-a512-9b06d03549ad

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGWH

namespace Sol_CGWH_weaklyHausdorffSpace_iff_isClosed_diagonal

/-- A subset of `Y` is closed for the `k`-ification of the topology of `Y` iff its preimage under
every continuous map from a compact Hausdorff space is closed. -/
theorem isClosed_compactlyGenerated_iff {Y : Type u} [TopologicalSpace Y] (s : Set Y) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} Y] s ↔
      ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (f : K → Y),
        Continuous f → IsClosed (f ⁻¹' s) := by
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  constructor
  · intro h K _ _ _ f hf
    exact h ⟨CompHaus.of K, ⟨f, hf⟩⟩
  · rintro h ⟨S, f⟩
    exact h S f f.continuous

/-- In a weakly Hausdorff space the image of a closed subset of a compact Hausdorff space under a
continuous map is closed. -/
theorem isClosed_image_of_weaklyHausdorff {X : Type u} [TopologicalSpace X]
    [WeaklyHausdorffSpace X] {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {f : K → X} (hf : Continuous f) {C : Set K} (hC : IsClosed C) : IsClosed (f '' C) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  have h := WeaklyHausdorffSpace.isClosed_range (X := X) C (f ∘ (Subtype.val : C → K))
    (hf.comp continuous_subtype_val)
  rwa [Set.range_comp, Subtype.range_coe] at h

/-- Points of a weakly Hausdorff space are closed. -/
theorem isClosed_singleton_of_weaklyHausdorff {X : Type u} [TopologicalSpace X]
    [WeaklyHausdorffSpace X] (x : X) : IsClosed ({x} : Set X) := by
  have h := WeaklyHausdorffSpace.isClosed_range (X := X) PUnit.{u + 1} (fun _ => x)
    continuous_const
  rwa [Set.range_const] at h

/-- Weakly Hausdorff implies `k`-closed diagonal (no hypothesis on `X`). -/
theorem isClosed_diagonal_of_weaklyHausdorff (X : Type u) [TopologicalSpace X]
    [WeaklyHausdorffSpace X] :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X) := by
  rw [isClosed_compactlyGenerated_iff]
  intro S _ _ _ g hg
  have hg₁ : Continuous fun s => (g s).1 := continuous_fst.comp hg
  have hg₂ : Continuous fun s => (g s).2 := continuous_snd.comp hg
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro s₀ hs₀
  have hne : (g s₀).1 ≠ (g s₀).2 := hs₀
  -- the test map `f : S ⊕ S → X`
  set f : S ⊕ S → X := Sum.elim (fun s => (g s).1) (fun s => (g s).2) with hf_def
  have hf : Continuous f := Continuous.sumElim hg₁ hg₂
  have hcx : IsClosed (f ⁻¹' {(g s₀).1}) :=
    (isClosed_singleton_of_weaklyHausdorff _).preimage hf
  have hcy : IsClosed (f ⁻¹' {(g s₀).2}) :=
    (isClosed_singleton_of_weaklyHausdorff _).preimage hf
  have hdisj : Disjoint (f ⁻¹' {(g s₀).1}) (f ⁻¹' {(g s₀).2}) := by
    rw [Set.disjoint_left]
    intro k hk₁ hk₂
    exact hne (hk₁.symm.trans hk₂)
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := normal_separation hcx hcy hdisj
  have hA : IsClosed (f '' Uᶜ) := isClosed_image_of_weaklyHausdorff hf hU.isClosed_compl
  have hB : IsClosed (f '' Vᶜ) := isClosed_image_of_weaklyHausdorff hf hV.isClosed_compl
  have hxA : (g s₀).1 ∉ f '' Uᶜ := by
    rintro ⟨k, hkU, hk⟩
    exact hkU (hxU hk)
  have hyB : (g s₀).2 ∉ f '' Vᶜ := by
    rintro ⟨k, hkV, hk⟩
    exact hkV (hyV hk)
  have hcover : ∀ k : S ⊕ S, f k ∈ f '' Uᶜ ∨ f k ∈ f '' Vᶜ := by
    intro k
    by_cases hk : k ∈ U
    · right
      exact ⟨k, fun hkV => Set.disjoint_left.mp hUV hk hkV, rfl⟩
    · left
      exact ⟨k, hk, rfl⟩
  have hW₁ : {s : S | (g s).1 ∈ (f '' Uᶜ)ᶜ} ∈ 𝓝 s₀ :=
    (hA.isOpen_compl.preimage hg₁).mem_nhds hxA
  have hW₂ : {s : S | (g s).2 ∈ (f '' Vᶜ)ᶜ} ∈ 𝓝 s₀ :=
    (hB.isOpen_compl.preimage hg₂).mem_nhds hyB
  filter_upwards [hW₁, hW₂] with s hs₁ hs₂
  intro hs
  have hs' : (g s).1 = (g s).2 := hs
  rcases hcover (Sum.inl s) with h | h
  · exact hs₁ h
  · have h2 : (g s).2 ∈ f '' Vᶜ := by
      have : f (Sum.inl s) = (g s).2 := hs'
      rwa [this] at h
    exact hs₂ h2

/-- A compactly generated space with `k`-closed diagonal is weakly Hausdorff. -/
theorem weaklyHausdorff_of_isClosed_diagonal (X : Type u) [TopologicalSpace X]
    [CompactlyGeneratedSpace X]
    (h : IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X)) :
    WeaklyHausdorffSpace X := by
  rw [isClosed_compactlyGenerated_iff] at h
  refine ⟨fun K _ _ _ f hf => ?_⟩
  refine CompactlyGeneratedSpace.isClosed' fun L _ _ _ g hg => ?_
  have hcl : IsClosed ((Prod.map f g) ⁻¹' Set.diagonal X) :=
    h (K × L) (Prod.map f g) (hf.prodMap hg)
  have himg : g ⁻¹' Set.range f = Prod.snd '' ((Prod.map f g) ⁻¹' Set.diagonal X) := by
    ext l
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨(k, l), hk, rfl⟩
    · rintro ⟨⟨k, l'⟩, hkl, rfl⟩
      exact ⟨k, hkl⟩
  rw [himg]
  exact (hcl.isCompact.image continuous_snd).isClosed

end Sol_CGWH_weaklyHausdorffSpace_iff_isClosed_diagonal

open Sol_CGWH_weaklyHausdorffSpace_iff_isClosed_diagonal

theorem solution
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedSpace X] :
    WeaklyHausdorffSpace X ↔
      IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X) :=
  ⟨fun _ => isClosed_diagonal_of_weaklyHausdorff X, weaklyHausdorff_of_isClosed_diagonal X⟩
