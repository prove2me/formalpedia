-- Prove2me | solution 1 for CGWH.isClosedEmbedding_and_isOpenEmbedding_snd_pullback
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:40:24.479036+00:00
-- url     : https://prove2.me/submissions/e644f005-1021-4af8-9ce0-ebda1d9d2a89

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_isClosedEmbedding_and_isOpenEmbedding_snd_pullback

/-- closed subspaces of compactly generated spaces are compactly generated -/
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

/-- open subspaces of compactly generated spaces are compactly generated -/
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

/-- the projection of the topological fibre product is an embedding when `f` is -/
theorem isEmbedding_snd {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] {f : X → Y} {g : T → Y} (hf : IsEmbedding f) (hg : Continuous g) :
    IsEmbedding (fun p : {p : X × T // f p.1 = g p.2} => p.1.2) := by
  have hG : IsEmbedding (fun t : T => (g t, t)) :=
    Function.LeftInverse.isEmbedding (f := Prod.snd) (fun _ => rfl) continuous_snd (by fun_prop)
  have hF : IsEmbedding (Prod.map f (id : T → T)) := hf.prodMap IsEmbedding.id
  have hcomp : IsEmbedding ((fun t : T => (g t, t)) ∘
      (fun p : {p : X × T // f p.1 = g p.2} => p.1.2)) := by
    have : ((fun t : T => (g t, t)) ∘ (fun p : {p : X × T // f p.1 = g p.2} => p.1.2)) =
        (Prod.map f (id : T → T)) ∘ Subtype.val := by
      funext p; simp [Prod.map, p.2]
    rw [this]; exact hF.comp IsEmbedding.subtypeVal
  exact IsEmbedding.of_comp (by fun_prop) (by fun_prop) hcomp

theorem range_snd {X Y T : Type u} {f : X → Y} {g : T → Y} :
    Set.range (fun p : {p : X × T // f p.1 = g p.2} => p.1.2) = g ⁻¹' Set.range f := by
  ext t; constructor
  · rintro ⟨p, rfl⟩; exact ⟨p.1.1, p.2⟩
  · rintro ⟨x, hx⟩; exact ⟨⟨(x, t), hx⟩, rfl⟩

end Sol_CGWH_isClosedEmbedding_and_isOpenEmbedding_snd_pullback

open CGWH Sol_CGWH_isClosedEmbedding_and_isOpenEmbedding_snd_pullback

theorem solution
    {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
    [CompactlyGeneratedSpace T] [WeaklyHausdorffSpace T]
    {f : X → Y} {g : T → Y} (hg : Continuous g) :
    (IsClosedEmbedding f →
        @IsClosedEmbedding {p : X × T // f p.1 = g p.2} T
          (TopologicalSpace.compactlyGenerated.{u} {p : X × T // f p.1 = g p.2}) _
          (fun p => p.1.2)) ∧
      (IsOpenEmbedding f →
        @IsOpenEmbedding {p : X × T // f p.1 = g p.2} T
          (TopologicalSpace.compactlyGenerated.{u} {p : X × T // f p.1 = g p.2}) _
          (fun p => p.1.2)) := by
  constructor
  · intro hf
    have h0 : IsClosedEmbedding (fun p : {p : X × T // f p.1 = g p.2} => p.1.2) :=
      ⟨isEmbedding_snd hf.isEmbedding hg, by rw [range_snd]; exact hf.isClosed_range.preimage hg⟩
    have := cg_of_isClosedEmbedding h0
    have heq := eq_compactlyGenerated.{u} (X := {p : X × T // f p.1 = g p.2})
    rw [← heq]; exact h0
  · intro hf
    have h0 : IsOpenEmbedding (fun p : {p : X × T // f p.1 = g p.2} => p.1.2) :=
      ⟨isEmbedding_snd hf.isEmbedding hg, by rw [range_snd]; exact hf.isOpen_range.preimage hg⟩
    have := cg_of_isOpenEmbedding h0
    have heq := eq_compactlyGenerated.{u} (X := {p : X × T // f p.1 = g p.2})
    rw [← heq]; exact h0

