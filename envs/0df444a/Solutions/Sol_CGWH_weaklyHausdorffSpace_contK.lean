-- Prove2me | solution 1 for CGWH.weaklyHausdorffSpace_contK
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:08:10.566326+00:00
-- url     : https://prove2.me/submissions/3e217f4f-153d-4cda-ba9d-db30dc7f14be

import Definitions.Def_CGWH_WeakHausdorff
import Definitions.Def_CGSpace_FunctionSpace

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGWH

namespace Sol_CGWH_weaklyHausdorffSpace_contK

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

/-- A continuous map stays continuous when the topology of its source is replaced by its
`k`-ification. -/
theorem continuous_of_compactlyGenerated {Z W : Type u} [t : TopologicalSpace Z]
    [TopologicalSpace W] {h : Z → W} (hh : Continuous h) :
    Continuous[TopologicalSpace.compactlyGenerated.{u} Z, _] h :=
  continuous_from_compactlyGenerated h fun _ g => hh.comp g.continuous

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

/-- Evaluation at a point `x : X`, as a map `C(X, Y) → Y`. -/
def ev {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (x : X) (φ : C(X, Y)) : Y := φ x

/-- Evaluation at a point is continuous for the compact-open topology defined by test maps. -/
theorem continuous_ev_probe (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] (x : X) :
    @Continuous C(X, Y) Y (CGSpace.probeCompactOpen X Y) _ (ev x) := by
  let _ : TopologicalSpace C(X, Y) := CGSpace.probeCompactOpen X Y
  refine continuous_def.mpr fun U hU => ?_
  refine TopologicalSpace.isOpen_generateFrom_of_mem ?_
  refine ⟨CompHaus.of PUnit.{u + 1}, ⟨fun _ => x, continuous_const⟩, U, hU, ?_⟩
  ext φ
  constructor
  · intro h _
    exact h
  · intro h
    exact h PUnit.unit

end Sol_CGWH_weaklyHausdorffSpace_contK

open Sol_CGWH_weaklyHausdorffSpace_contK

theorem solution
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y] :
    WeaklyHausdorffSpace (CGSpace.ContK X Y) := by
  -- evaluation at a point is continuous on `ContK X Y`
  have hevK : ∀ x : X, Continuous (fun φ : CGSpace.ContK X Y => ev x φ) := by
    intro x
    exact @continuous_of_compactlyGenerated C(X, Y) Y (CGSpace.probeCompactOpen X Y) _
      (ev x) (continuous_ev_probe X Y x)
  refine ⟨fun K _ _ _ f hf => ?_⟩
  change IsClosed[@TopologicalSpace.compactlyGenerated.{u} C(X, Y) (CGSpace.probeCompactOpen X Y)]
    (Set.range f)
  rw [@isClosed_compactlyGenerated_iff C(X, Y) (CGSpace.probeCompactOpen X Y)]
  intro S _ _ _ g hg
  -- the coincidence set of `g` and `f` in `S × K`
  have hE : IsClosed {p : S × K | g p.1 = f p.2} := by
    have hEq : {p : S × K | g p.1 = f p.2} =
        ⋂ x : X, {p : S × K | ev x (g p.1) = ev x (f p.2)} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h x => by rw [h], fun h => ContinuousMap.ext h⟩
    rw [hEq]
    refine isClosed_iInter fun x => ?_
    have ha : Continuous (fun p : S × K => ev x (g p.1)) :=
      (@Continuous.comp S C(X, Y) Y _ (CGSpace.probeCompactOpen X Y) _ _ _
        (continuous_ev_probe X Y x) hg).comp continuous_fst
    have hb : Continuous (fun p : S × K => ev x (f p.2)) :=
      ((hevK x).comp hf).comp continuous_snd
    exact isClosed_setOf_eq_of_compact ha hb
  have himg : g ⁻¹' Set.range f = Prod.fst '' {p : S × K | g p.1 = f p.2} := by
    ext s
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨(s, k), hk.symm, rfl⟩
    · rintro ⟨⟨s', k⟩, hsk, rfl⟩
      exact ⟨k, hsk.symm⟩
  rw [himg]
  exact (hE.isCompact.image continuous_fst).isClosed
