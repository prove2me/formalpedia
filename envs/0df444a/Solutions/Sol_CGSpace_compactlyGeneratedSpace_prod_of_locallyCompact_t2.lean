-- Prove2me | solution 1 for CGSpace.compactlyGeneratedSpace_prod_of_locallyCompact_t2
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:57:16.073248+00:00
-- url     : https://prove2.me/submissions/bcdac40e-9284-4e75-88ae-721edc633727

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

theorem solution
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] [LocallyCompactSpace Y] [T2Space Y] :
    CompactlyGeneratedSpace (X × Y) := by
  -- It suffices to show that a set `W` whose preimage under every continuous map from a
  -- compact Hausdorff space is open, is open.
  refine compactlyGeneratedSpace_of_isOpen fun W hW ↦ ?_
  rw [isOpen_iff_mem_nhds]
  rintro ⟨x₀, y₀⟩ hxy
  -- Step 1: the slice `{y | (x₀, y) ∈ W}` is a neighbourhood of `y₀`.
  have hslice : {y : Y | (x₀, y) ∈ W} ∈ 𝓝 y₀ := by
    obtain ⟨C, hC, hCy⟩ := exists_compact_mem_nhds y₀
    have : CompactSpace C := isCompact_iff_compactSpace.1 hC
    have hg : Continuous (fun c : C ↦ ((x₀, (c : Y)) : X × Y)) :=
      continuous_const.prodMk continuous_subtype_val
    have hopen : IsOpen ((fun c : C ↦ ((x₀, (c : Y)) : X × Y)) ⁻¹' W) := hW C _ hg
    have hy₀C : y₀ ∈ C := mem_of_mem_nhds hCy
    have hmem : (fun c : C ↦ ((x₀, (c : Y)) : X × Y)) ⁻¹' W ∈ 𝓝 (⟨y₀, hy₀C⟩ : C) :=
      hopen.mem_nhds hxy
    have himage : Subtype.val '' ((fun c : C ↦ ((x₀, (c : Y)) : X × Y)) ⁻¹' W) ∈ 𝓝 y₀ := by
      rw [← map_nhds_subtype_coe_eq_nhds hy₀C hCy]
      exact Filter.image_mem_map hmem
    refine Filter.mem_of_superset himage ?_
    rintro _ ⟨c, hc, rfl⟩
    exact hc
  -- Step 2: a compact neighbourhood `L` of `y₀` with `{x₀} × L ⊆ W`.
  obtain ⟨L, hLy, hLW, hL⟩ := local_compact_nhds hslice
  have : CompactSpace L := isCompact_iff_compactSpace.1 hL
  -- Step 3: `U = {x | {x} × L ⊆ W}` is open in `X`, because `X` is compactly generated
  -- and by the tube lemma on `K × L` for every compact Hausdorff test space `K`.
  have hU : IsOpen {x : X | ∀ l : L, (x, (l : Y)) ∈ W} := by
    refine CompactlyGeneratedSpace.isOpen' fun K _ _ _ f hf ↦ ?_
    have hg : Continuous (fun p : K × L ↦ ((f p.1, (p.2 : Y)) : X × Y)) :=
      (hf.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    have hopen : IsOpen ((fun p : K × L ↦ ((f p.1, (p.2 : Y)) : X × Y)) ⁻¹' W) :=
      hW (K × L) _ hg
    rw [isOpen_iff_mem_nhds]
    intro k hk
    have hk' : ∀ l : L, (f k, (l : Y)) ∈ W := hk
    have key : ∀ᶠ k' in 𝓝 k, ∀ l ∈ (Set.univ : Set L), (f k', (l : Y)) ∈ W := by
      refine isCompact_univ.eventually_forall_of_forall_eventually fun l _ ↦ ?_
      exact hopen.mem_nhds (hk' l)
    refine Filter.mem_of_superset key ?_
    intro k' hk'' l
    exact hk'' l (Set.mem_univ l)
  -- Step 4: `U × L` is a neighbourhood of `(x₀, y₀)` contained in `W`.
  have hx₀ : x₀ ∈ {x : X | ∀ l : L, (x, (l : Y)) ∈ W} := fun l ↦ hLW l.2
  refine Filter.mem_of_superset (prod_mem_nhds (hU.mem_nhds hx₀) hLy) ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact hx ⟨y, hy⟩
