-- Prove2me | solution 1 for CGWH.isClosedEmbedding_of_comp_and_isLocallyClosed_range_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:39:22.854177+00:00
-- url     : https://prove2.me/submissions/67a39453-a42e-45c9-8dcc-d0af228d6cda

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_isClosed_setOf_eq

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGWH

namespace Sol_CGWH_isClosedEmbedding_of_comp_and_isLocallyClosed_range_of_comp

/-- Closed subspaces of compactly generated spaces are compactly generated. -/
theorem cg_of_isClosedEmbedding {A T : Type u} [TopologicalSpace A] [TopologicalSpace T]
    [CompactlyGeneratedSpace T] {e : A → T} (he : IsClosedEmbedding e) :
    CompactlyGeneratedSpace A := by
  refine compactlyGeneratedSpace_of_isClosed fun s hs => ?_
  have hes : IsClosed (e '' s) := by
    refine CompactlyGeneratedSpace.isClosed' fun K _ _ _ h hh => ?_
    let K' : Set K := h ⁻¹' Set.range e
    have hK' : IsClosed K' := he.isClosed_range.preimage hh
    have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'.isCompact
    let h' : K' → A := fun k => Classical.choose k.2
    have hh' : ∀ k : K', e (h' k) = h k := fun k => Classical.choose_spec k.2
    have hcont : Continuous h' := by
      rw [he.isEmbedding.continuous_iff]
      have : e ∘ h' = fun k : K' => h k := funext hh'
      rw [this]; exact hh.comp continuous_subtype_val
    have h1 := hs K' h' hcont
    have h2 := hK'.isClosedEmbedding_subtypeVal.isClosedMap _ h1
    convert h2 using 1
    ext k; constructor
    · rintro ⟨a, ha, hak⟩
      have hk : k ∈ K' := ⟨a, hak⟩
      refine ⟨⟨k, hk⟩, ?_, rfl⟩
      have : h' ⟨k, hk⟩ = a := he.injective ((hh' ⟨k, hk⟩).trans hak.symm)
      change h' ⟨k, hk⟩ ∈ s
      rw [this]; exact ha
    · rintro ⟨k', hk', rfl⟩
      exact ⟨h' k', hk', hh' k'⟩
  have := hes.preimage he.continuous
  rwa [Set.preimage_image_eq _ he.injective] at this

/-- Open subspaces of compactly generated spaces are compactly generated. -/
theorem cg_of_isOpenEmbedding {A T : Type u} [TopologicalSpace A] [TopologicalSpace T]
    [CompactlyGeneratedSpace T] {e : A → T} (he : IsOpenEmbedding e) :
    CompactlyGeneratedSpace A := by
  refine compactlyGeneratedSpace_of_isOpen fun s hs => ?_
  have hes : IsOpen (e '' s) := by
    refine CompactlyGeneratedSpace.isOpen' fun K _ _ _ h hh => ?_
    rw [isOpen_iff_mem_nhds]
    intro k hk
    have hV : IsOpen (h ⁻¹' Set.range e) := he.isOpen_range.preimage hh
    have hkV : k ∈ h ⁻¹' Set.range e := by
      obtain ⟨a, -, ha⟩ := hk; exact ⟨a, ha⟩
    obtain ⟨L, hLnhds, hLsub, hLcomp⟩ := local_compact_nhds (hV.mem_nhds hkV)
    have : CompactSpace L := isCompact_iff_compactSpace.mp hLcomp
    let h' : L → A := fun l => Classical.choose (hLsub l.2)
    have hh' : ∀ l : L, e (h' l) = h l := fun l => Classical.choose_spec (hLsub l.2)
    have hcont : Continuous h' := by
      rw [he.isEmbedding.continuous_iff]
      have : e ∘ h' = fun l : L => h l := funext hh'
      rw [this]; exact hh.comp continuous_subtype_val
    have h1 := hs L h' hcont
    obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp h1
    have hkL : k ∈ L := mem_of_mem_nhds hLnhds
    have hkO : k ∈ O := by
      have : (⟨k, hkL⟩ : L) ∈ Subtype.val ⁻¹' O := by
        rw [hOeq]
        obtain ⟨a, ha, hak⟩ := hk
        have : h' ⟨k, hkL⟩ = a := he.injective ((hh' ⟨k, hkL⟩).trans hak.symm)
        change h' ⟨k, hkL⟩ ∈ s
        rw [this]; exact ha
      exact this
    refine Filter.mem_of_superset (Filter.inter_mem hLnhds (hO.mem_nhds hkO)) ?_
    rintro l ⟨hlL, hlO⟩
    have : (⟨l, hlL⟩ : L) ∈ h' ⁻¹' s := by rw [← hOeq]; exact hlO
    exact ⟨h' ⟨l, hlL⟩, this, hh' ⟨l, hlL⟩⟩
  have := hes.preimage he.continuous
  rwa [Set.preimage_image_eq _ he.injective] at this

end Sol_CGWH_isClosedEmbedding_of_comp_and_isLocallyClosed_range_of_comp

open Sol_CGWH_isClosedEmbedding_of_comp_and_isLocallyClosed_range_of_comp in
theorem solution
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
    [CompactlyGeneratedSpace Z] [WeaklyHausdorffSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    (IsClosedEmbedding (g ∘ f) → IsClosedEmbedding f) ∧
      (IsOpenEmbedding (g ∘ f) → IsEmbedding f ∧ IsLocallyClosed (Set.range f)) := by
  -- common part: on Y' = g ⁻¹' range (g ∘ f), the range of f is a coincidence set
  have common : IsEmbedding (g ∘ f) → CompactlyGeneratedSpace (g ⁻¹' Set.range (g ∘ f)) →
      ∃ C : Set Y, IsClosed C ∧ Set.range f = (g ⁻¹' Set.range (g ∘ f)) ∩ C := by
    intro hgf hCG
    let Y' : Set Y := g ⁻¹' Set.range (g ∘ f)
    let ψ : Y' → X := fun y => Classical.choose y.2
    have hψ : ∀ y : Y', g (f (ψ y)) = g y := fun y => Classical.choose_spec y.2
    have hψc : Continuous ψ := by
      rw [hgf.continuous_iff]
      have : (g ∘ f) ∘ ψ = fun y : Y' => g y := funext hψ
      rw [this]; exact hg.comp continuous_subtype_val
    have hcl : IsClosed {y : Y' | f (ψ y) = (y : Y)} :=
      CGWH.isClosed_setOf_eq (hf.comp hψc) continuous_subtype_val
    obtain ⟨C, hC, hCeq⟩ := isClosed_induced_iff.mp hcl
    refine ⟨C, hC, ?_⟩
    ext y; constructor
    · rintro ⟨x, rfl⟩
      have hy : f x ∈ Y' := ⟨x, rfl⟩
      refine ⟨hy, ?_⟩
      have : (⟨f x, hy⟩ : Y') ∈ Subtype.val ⁻¹' C := by
        rw [hCeq]
        have : ψ ⟨f x, hy⟩ = x := hgf.injective (hψ ⟨f x, hy⟩)
        change f (ψ ⟨f x, hy⟩) = f x
        rw [this]
      exact this
    · rintro ⟨hy, hyC⟩
      have : (⟨y, hy⟩ : Y') ∈ {y : Y' | f (ψ y) = (y : Y)} := by rw [← hCeq]; exact hyC
      exact ⟨ψ ⟨y, hy⟩, this⟩
  constructor
  · intro h
    refine ⟨IsEmbedding.of_comp hf hg h.isEmbedding, ?_⟩
    have hY' : IsClosed (g ⁻¹' Set.range (g ∘ f)) := h.isClosed_range.preimage hg
    obtain ⟨C, hC, hCeq⟩ := common h.isEmbedding
      (cg_of_isClosedEmbedding hY'.isClosedEmbedding_subtypeVal)
    rw [hCeq]; exact hY'.inter hC
  · intro h
    refine ⟨IsEmbedding.of_comp hf hg h.isEmbedding, ?_⟩
    have hY' : IsOpen (g ⁻¹' Set.range (g ∘ f)) := h.isOpen_range.preimage hg
    obtain ⟨C, hC, hCeq⟩ := common h.isEmbedding
      (cg_of_isOpenEmbedding hY'.isOpenEmbedding_subtypeVal)
    exact ⟨_, C, hY', hC, hCeq⟩
