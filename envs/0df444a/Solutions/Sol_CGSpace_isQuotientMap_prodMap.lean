-- Prove2me | solution 1 for CGSpace.isQuotientMap_prodMap
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:11:09.334262+00:00
-- url     : https://prove2.me/submissions/75696a87-30d1-4b03-83ad-3898cc98d9bc

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGSpace_isQuotientMap_prodMap

/-- A set is open for the `k`-ification of a topology if and only if its preimage under every
continuous map from a compact Hausdorff space is open. -/
theorem isOpen_kTop_iff {W : Type u} [TopologicalSpace W] {s : Set W} :
    IsOpen[compactlyGenerated.{u} W] s ↔
      ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (c : K → W),
        Continuous c → IsOpen (c ⁻¹' s) := by
  constructor
  · intro hs K _ _ _ c hc
    rw [compactlyGenerated, isOpen_coinduced, isOpen_sigma_iff] at hs
    exact hs ⟨CompHaus.of K, ⟨c, hc⟩⟩
  · intro h
    rw [compactlyGenerated, isOpen_coinduced, isOpen_sigma_iff]
    rintro ⟨S, c⟩
    exact h S c c.continuous

/-- The product of a compactly generated space and a locally compact Hausdorff space is
compactly generated (for the product topology). -/
theorem compactlyGeneratedSpace_prod
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

/-- One-sided statement, left factor: if `f : X → X'` is a quotient map with `X` compactly
generated, a subset of `X' × Y` whose preimage under `f × id` is `k`-open is `k`-open. -/
theorem isOpen_kTop_of_preimage_left {X X' Y : Type u} [TopologicalSpace X]
    [TopologicalSpace X'] [TopologicalSpace Y] [CompactlyGeneratedSpace X]
    {f : X → X'} (hf : IsQuotientMap f) {U : Set (X' × Y)}
    (hU : IsOpen[compactlyGenerated.{u} (X × Y)] (Prod.map f id ⁻¹' U)) :
    IsOpen[compactlyGenerated.{u} (X' × Y)] U := by
  rw [isOpen_kTop_iff] at hU ⊢
  intro S _ _ _ c hc
  -- `T = (id × c₂)⁻¹ U ⊆ X' × S` is open for the product topology (Whitehead's lemma).
  have hT : IsOpen {p : X' × S | (p.1, (c p.2).2) ∈ U} := by
    rw [isOpen_iff_continuous_mem]
    refine hf.continuous_lift_prod_left (Y := S)
      (g := fun p : X' × S ↦ (p.1, (c p.2).2) ∈ U) ?_
    have hopen : IsOpen {p : X × S | (f p.1, (c p.2).2) ∈ U} := by
      have : CompactlyGeneratedSpace (X × S) := compactlyGeneratedSpace_prod X S
      refine CompactlyGeneratedSpace.isOpen' fun K _ _ _ d hd ↦ ?_
      have hcont : Continuous (fun k : K ↦ (((d k).1, (c (d k).2).2) : X × Y)) :=
        (continuous_fst.comp hd).prodMk (continuous_snd.comp (hc.comp (continuous_snd.comp hd)))
      exact hU K _ hcont
    exact isOpen_iff_continuous_mem.1 hopen
  have hcont : Continuous (fun s : S ↦ (((c s).1, s) : X' × S)) :=
    (continuous_fst.comp hc).prodMk continuous_id
  exact hT.preimage hcont

/-- One-sided statement, right factor. -/
theorem isOpen_kTop_of_preimage_right {X Y Y' : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Y'] [CompactlyGeneratedSpace Y]
    {g : Y → Y'} (hg : IsQuotientMap g) {U : Set (X × Y')}
    (hU : IsOpen[compactlyGenerated.{u} (X × Y)] (Prod.map id g ⁻¹' U)) :
    IsOpen[compactlyGenerated.{u} (X × Y')] U := by
  rw [isOpen_kTop_iff] at hU ⊢
  intro S _ _ _ c hc
  have hT : IsOpen {p : Y' × S | ((c p.2).1, p.1) ∈ U} := by
    rw [isOpen_iff_continuous_mem]
    refine hg.continuous_lift_prod_left (Y := S)
      (g := fun p : Y' × S ↦ ((c p.2).1, p.1) ∈ U) ?_
    have hopen : IsOpen {p : Y × S | ((c p.2).1, g p.1) ∈ U} := by
      have : CompactlyGeneratedSpace (Y × S) := compactlyGeneratedSpace_prod Y S
      refine CompactlyGeneratedSpace.isOpen' fun K _ _ _ d hd ↦ ?_
      have hcont : Continuous (fun k : K ↦ (((c (d k).2).1, (d k).1) : X × Y)) :=
        (continuous_fst.comp (hc.comp (continuous_snd.comp hd))).prodMk (continuous_fst.comp hd)
      exact hU K _ hcont
    exact isOpen_iff_continuous_mem.1 hopen
  have hcont : Continuous (fun s : S ↦ (((c s).2, s) : Y' × S)) :=
    (continuous_snd.comp hc).prodMk continuous_id
  exact hT.preimage hcont

end Sol_CGSpace_isQuotientMap_prodMap

open Sol_CGSpace_isQuotientMap_prodMap in
theorem solution
    {X X' Y Y' : Type u} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
    [TopologicalSpace Y'] [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y]
    [CompactlyGeneratedSpace X'] [CompactlyGeneratedSpace Y']
    {f : X → X'} {g : Y → Y'} (hf : IsQuotientMap f) (hg : IsQuotientMap g) :
    @IsQuotientMap (X × Y) (X' × Y') (TopologicalSpace.compactlyGenerated.{u} (X × Y))
      (TopologicalSpace.compactlyGenerated.{u} (X' × Y')) (Prod.map f g) := by
  refine @IsQuotientMap.mk _ _ (compactlyGenerated.{u} (X × Y))
    (compactlyGenerated.{u} (X' × Y')) _ ?_ (hf.surjective.prodMap hg.surjective)
  refine @IsCoinducing.mk _ _ (compactlyGenerated.{u} (X × Y))
    (compactlyGenerated.{u} (X' × Y')) _ ?_
  refine TopologicalSpace.ext_iff.2 fun U ↦ ?_
  have key : IsOpen[compactlyGenerated.{u} (X' × Y')] U ↔
      IsOpen[compactlyGenerated.{u} (X × Y)] (Prod.map f g ⁻¹' U) := by
    refine ⟨fun hU ↦ ?_, fun hU ↦ ?_⟩
    · -- `f × g` is continuous for the `k`-ified product topologies.
      rw [isOpen_kTop_iff] at hU ⊢
      intro K _ _ _ c hc
      exact hU K (Prod.map f g ∘ c) ((hf.continuous.prodMap hg.continuous).comp hc)
    · -- A set with `k`-open preimage is `k`-open: factor `f × g = (f × id) ∘ (id × g)`.
      refine isOpen_kTop_of_preimage_left hf ?_
      refine isOpen_kTop_of_preimage_right hg ?_
      exact hU
  exact key
