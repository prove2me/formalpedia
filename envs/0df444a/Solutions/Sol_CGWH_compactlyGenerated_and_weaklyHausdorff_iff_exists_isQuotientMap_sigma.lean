-- Prove2me | solution 1 for CGWH.compactlyGenerated_and_weaklyHausdorff_iff_exists_isQuotientMap_sigma
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:02:37.496276+00:00
-- url     : https://prove2.me/submissions/1d1a617a-8e45-404e-9cb6-f25069cb12fb

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_compactlyGenerated_and_weaklyHausdorff_iff_exists_isQuotientMap_sigma

/-- In a weakly Hausdorff space every point is closed: `{x}` is the image of the one-point space. -/
theorem isClosed_singleton_of_weaklyHausdorff {K : Type u} [TopologicalSpace K]
    [CGWH.WeaklyHausdorffSpace K] (x : K) : IsClosed ({x} : Set K) := by
  have hx := CGWH.WeaklyHausdorffSpace.isClosed_range PUnit.{u+1} (fun _ => x) continuous_const
  rwa [Set.range_const] at hx

/-- A continuous map from a compact Hausdorff space to a weakly Hausdorff space is a closed map:
a closed subset `C` of the source is itself a compact Hausdorff space, and its image is the range
of the restriction of the map to `C`. -/
theorem isClosedMap_of_weaklyHausdorff {K K' : Type u} [TopologicalSpace K]
    [CGWH.WeaklyHausdorffSpace K] [TopologicalSpace K'] [CompactSpace K'] [T2Space K']
    {q : K' → K} (hq : Continuous q) : IsClosedMap q := by
  intro C hC
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  have h := CGWH.WeaklyHausdorffSpace.isClosed_range C (fun c : C => q c.1)
    (hq.comp continuous_subtype_val)
  have hrange : Set.range (fun c : C => q c.1) = q '' C := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  rwa [hrange] at h

/-- A weakly Hausdorff space which is the continuous image of a compact Hausdorff space is
Hausdorff (Lemma E.2.1.4 of the source). -/
theorem t2Space_of_surjective {K K' : Type u} [TopologicalSpace K] [CGWH.WeaklyHausdorffSpace K]
    [TopologicalSpace K'] [CompactSpace K'] [T2Space K']
    {q : K' → K} (hq : Continuous q) (hs : Function.Surjective q) : T2Space K := by
  have hcl : IsClosedMap q := isClosedMap_of_weaklyHausdorff hq
  refine ⟨fun x y hxy => ?_⟩
  -- the two fibres are disjoint closed subsets of the normal space `K'`
  have hFx : IsClosed (q ⁻¹' {x}) := (isClosed_singleton_of_weaklyHausdorff x).preimage hq
  have hFy : IsClosed (q ⁻¹' {y}) := (isClosed_singleton_of_weaklyHausdorff y).preimage hq
  have hdisj : Disjoint (q ⁻¹' {x}) (q ⁻¹' {y}) := by
    rw [Set.disjoint_left]
    intro w hwx hwy
    exact hxy ((Set.mem_singleton_iff.mp hwx).symm.trans (Set.mem_singleton_iff.mp hwy))
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := (normal_separation hFx hFy hdisj :
    SeparatedNhds (q ⁻¹' {x}) (q ⁻¹' {y}))
  -- push the separating open sets down along the closed map `q`
  refine ⟨(q '' Uᶜ)ᶜ, (q '' Vᶜ)ᶜ, (hcl _ hU.isClosed_compl).isOpen_compl,
    (hcl _ hV.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · rintro ⟨w, hwU, hwx⟩
    exact hwU (hxU (Set.mem_singleton_iff.mpr hwx))
  · rintro ⟨w, hwV, hwy⟩
    exact hwV (hyV (Set.mem_singleton_iff.mpr hwy))
  · rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨w, rfl⟩ := hs z
    have hwU : w ∈ U := by
      by_contra h
      exact hzU ⟨w, h, rfl⟩
    have hwV : w ∈ V := by
      by_contra h
      exact hzV ⟨w, h, rfl⟩
    exact Set.disjoint_left.mp hUV hwU hwV

/-- Every subspace of a weakly Hausdorff space is weakly Hausdorff: the range of a test map into
the subspace is the trace of the range of its composition with the inclusion. -/
theorem weaklyHausdorffSpace_subtype {X : Type u} [TopologicalSpace X]
    [CGWH.WeaklyHausdorffSpace X] (s : Set X) : CGWH.WeaklyHausdorffSpace s := by
  refine ⟨fun K _ _ _ g hg => ?_⟩
  have h := CGWH.WeaklyHausdorffSpace.isClosed_range K (fun k => (g k : X))
    (continuous_subtype_val.comp hg)
  have hrange : Set.range g = Subtype.val ⁻¹' (Set.range (fun k => (g k : X))) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
  rw [hrange]
  exact h.preimage continuous_subtype_val

/-- The range of a continuous map from a compact Hausdorff space to a weakly Hausdorff space is a
closed compact Hausdorff subspace. -/
theorem range_isClosed_isCompact_t2 {X S : Type u} [TopologicalSpace X]
    [CGWH.WeaklyHausdorffSpace X] [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {f : S → X} (hf : Continuous f) :
    IsClosed (Set.range f) ∧ IsCompact (Set.range f) ∧ T2Space (Set.range f) := by
  refine ⟨CGWH.WeaklyHausdorffSpace.isClosed_range S f hf, isCompact_range hf, ?_⟩
  have : CGWH.WeaklyHausdorffSpace (Set.range f) := weaklyHausdorffSpace_subtype (Set.range f)
  have hcont : Continuous (fun s : S => (⟨f s, Set.mem_range_self s⟩ : Set.range f)) :=
    hf.subtype_mk _
  refine t2Space_of_surjective hcont ?_
  rintro ⟨_, s, rfl⟩
  exact ⟨s, rfl⟩

/-- (1) ⟹ (2): a compactly generated weakly Hausdorff space is the quotient of the disjoint union
of all its closed compact Hausdorff subspaces. -/
theorem exists_isQuotientMap_sigma (X : Type u) [TopologicalSpace X] [CompactlyGeneratedSpace X]
    [CGWH.WeaklyHausdorffSpace X] :
    ∃ I : Set (Set X), (∀ K ∈ I, IsClosed K ∧ IsCompact K ∧ T2Space K) ∧
      IsQuotientMap (fun p : (Σ K : I, (K : Set X)) => (p.2 : X)) := by
  refine ⟨{K : Set X | IsClosed K ∧ IsCompact K ∧ T2Space K}, fun K hK => hK, ?_⟩
  have hcont : Continuous
      (fun p : (Σ K : {K : Set X | IsClosed K ∧ IsCompact K ∧ T2Space K}, (K : Set X)) =>
        (p.2 : X)) :=
    continuous_sigma fun _ => continuous_subtype_val
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen fun U =>
    ⟨fun hU => ?_, fun hU => hU.preimage hcont⟩, fun x => ?_⟩
  swap
  · -- the point `x` lies in the closed compact Hausdorff subspace `{x}`
    have hx : ({x} : Set X) ∈ {K : Set X | IsClosed K ∧ IsCompact K ∧ T2Space K} := by
      refine ⟨isClosed_singleton_of_weaklyHausdorff x, isCompact_singleton, ?_⟩
      infer_instance
    exact ⟨⟨⟨{x}, hx⟩, ⟨x, rfl⟩⟩, rfl⟩
  · -- a test map `f : S → X` factors through the summand `range f`
    refine CompactlyGeneratedSpace.isOpen' fun S _ _ _ f hf => ?_
    have hK : Set.range f ∈ {K : Set X | IsClosed K ∧ IsCompact K ∧ T2Space K} :=
      range_isClosed_isCompact_t2 hf
    have hlift : Continuous (fun s : S =>
        (⟨⟨Set.range f, hK⟩, ⟨f s, Set.mem_range_self s⟩⟩ :
          Σ K : {K : Set X | IsClosed K ∧ IsCompact K ∧ T2Space K}, (K : Set X))) :=
      (continuous_sigmaMk (σ := fun K : {K : Set X | IsClosed K ∧ IsCompact K ∧ T2Space K} =>
        ((K : Set X) : Type u)) (i := ⟨Set.range f, hK⟩)).comp (hf.subtype_mk _)
    exact hU.preimage hlift

/-- (2) ⟹ (1), compact generation: the inclusions of the members of `I` are test maps. -/
theorem compactlyGeneratedSpace_of_isQuotientMap_sigma {X : Type u} [TopologicalSpace X]
    {I : Set (Set X)} (hI : ∀ K ∈ I, IsClosed K ∧ IsCompact K ∧ T2Space K)
    (hq : IsQuotientMap (fun p : (Σ K : I, (K : Set X)) => (p.2 : X))) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isOpen fun s hs => ?_
  rw [← hq.isCoinducing.isOpen_preimage, isOpen_sigma_iff]
  intro K
  have : CompactSpace (K : Set X) := isCompact_iff_compactSpace.mp (hI K K.2).2.1
  have : T2Space (K : Set X) := (hI K K.2).2.2
  exact hs (K : Set X) Subtype.val continuous_subtype_val

/-- (2) ⟹ (1), weak Hausdorff property: the trace of the image of a test map on a member `K` of
`I` is a compact subset of the Hausdorff space `K`. -/
theorem weaklyHausdorffSpace_of_isQuotientMap_sigma {X : Type u} [TopologicalSpace X]
    {I : Set (Set X)} (hI : ∀ K ∈ I, IsClosed K ∧ IsCompact K ∧ T2Space K)
    (hq : IsQuotientMap (fun p : (Σ K : I, (K : Set X)) => (p.2 : X))) :
    CGWH.WeaklyHausdorffSpace X := by
  refine ⟨fun S _ _ _ f hf => ?_⟩
  rw [← hq.isCoinducing.isClosed_preimage, isClosed_sigma_iff]
  intro K
  have hT2 : T2Space (K : Set X) := (hI K K.2).2.2
  have hcompact : IsCompact (Subtype.val ⁻¹' Set.range f : Set (K : Set X)) := by
    rw [IsInducing.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
      ← Set.image_preimage_eq_inter_range]
    exact (((hI K K.2).1.preimage hf).isCompact).image hf
  exact hcompact.isClosed

end Sol_CGWH_compactlyGenerated_and_weaklyHausdorff_iff_exists_isQuotientMap_sigma

open CGWH Sol_CGWH_compactlyGenerated_and_weaklyHausdorff_iff_exists_isQuotientMap_sigma

theorem solution
    (X : Type u) [TopologicalSpace X] :
    (CompactlyGeneratedSpace X ∧ WeaklyHausdorffSpace X) ↔
      ∃ I : Set (Set X), (∀ K ∈ I, IsClosed K ∧ IsCompact K ∧ T2Space K) ∧
        IsQuotientMap (fun p : (Σ K : I, (K : Set X)) => (p.2 : X)) := by
  constructor
  · rintro ⟨hCG, hWH⟩
    exact exists_isQuotientMap_sigma X
  · rintro ⟨I, hI, hq⟩
    exact ⟨compactlyGeneratedSpace_of_isQuotientMap_sigma hI hq,
      weaklyHausdorffSpace_of_isQuotientMap_sigma hI hq⟩
