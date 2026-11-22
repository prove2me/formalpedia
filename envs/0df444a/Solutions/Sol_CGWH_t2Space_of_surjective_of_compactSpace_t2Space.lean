-- Prove2me | solution 1 for CGWH.t2Space_of_surjective_of_compactSpace_t2Space
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:53:03.938046+00:00
-- url     : https://prove2.me/submissions/64ef6193-348d-410d-ba8b-127760621167

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_t2Space_of_surjective_of_compactSpace_t2Space

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

end Sol_CGWH_t2Space_of_surjective_of_compactSpace_t2Space

open CGWH Sol_CGWH_t2Space_of_surjective_of_compactSpace_t2Space

theorem solution
    {K K' : Type u} [TopologicalSpace K] [WeaklyHausdorffSpace K]
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
