-- Prove2me | solution 1 for CGWH.weaklyHausdorffSpace_quotient_iff
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:56:19.253591+00:00
-- url     : https://prove2.me/submissions/2df53141-d621-4f0a-b574-2ea6b73a9ab6

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_weaklyHausdorffSpace_quotient_iff

/-- Closed sets of the `k`-ification: a set is `k`-closed iff its preimage under every test map
is closed. -/
theorem isClosed_compactlyGenerated_iff {Y : Type u} [TopologicalSpace Y] (s : Set Y) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} Y] s ↔
      ∀ (K : CompHaus.{u}) (f : C(K, Y)), IsClosed (f ⁻¹' s) := by
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  exact ⟨fun h K f => h ⟨K, f⟩, fun h ⟨K, f⟩ => h K f⟩

/-- The coincidence set of two continuous maps from a compact Hausdorff space to a weakly
Hausdorff space is closed. -/
theorem isClosed_setOf_eq_of_weaklyHausdorff {Q : Type u} [TopologicalSpace Q]
    [CGWH.WeaklyHausdorffSpace Q] {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {g₁ g₂ : K → Q} (h₁ : Continuous g₁) (h₂ : Continuous g₂) :
    IsClosed {k : K | g₁ k = g₂ k} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro k hk
  have hk' : g₁ k ≠ g₂ k := hk
  -- points of `Q` are closed
  have hpt : IsClosed ({g₂ k} : Set Q) := by
    have h := CGWH.WeaklyHausdorffSpace.isClosed_range PUnit.{u + 1} (fun _ => g₂ k)
      continuous_const
    rwa [Set.range_const] at h
  have hU : g₁ ⁻¹' ({g₂ k} : Set Q)ᶜ ∈ 𝓝 k := (hpt.isOpen_compl.preimage h₁).mem_nhds hk'
  -- a closed neighbourhood `C` of `k` on which `g₁` avoids `g₂ k`
  obtain ⟨C, hCk, hCcl, hCU⟩ := exists_mem_nhds_isClosed_subset hU
  have : CompactSpace C := isCompact_iff_compactSpace.mp hCcl.isCompact
  have himg : IsClosed (g₁ '' C) := by
    have h := CGWH.WeaklyHausdorffSpace.isClosed_range C (fun c : C => g₁ c)
      (h₁.comp continuous_subtype_val)
    have e : Set.range (fun c : C => g₁ c) = g₁ '' C := by
      ext y
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨c, c.2, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨⟨c, hc⟩, rfl⟩
    rwa [e] at h
  have hnot : g₂ k ∉ g₁ '' C := by
    rintro ⟨c, hc, hcq⟩
    exact hCU hc hcq
  have hW : g₂ ⁻¹' (g₁ '' C)ᶜ ∈ 𝓝 k := (himg.isOpen_compl.preimage h₂).mem_nhds hnot
  filter_upwards [hCk, hW] with a haC haW heq
  exact haW ⟨a, haC, heq⟩

/-- A compactly generated space is the quotient of the disjoint union of all its test maps. -/
theorem isQuotientMap_sigma {X : Type u} [TopologicalSpace X] [CompactlyGeneratedSpace X] :
    IsQuotientMap (fun p : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) => p.1.2 p.2) := by
  refine ⟨⟨?_⟩, fun x => ?_⟩
  · exact eq_compactlyGenerated
  · exact ⟨⟨⟨CompHaus.of PUnit.{u + 1}, ContinuousMap.const _ x⟩, PUnit.unit⟩, rfl⟩

/-- If the graph of the equivalence relation is `k`-closed in `X × X`, the quotient is weakly
Hausdorff. -/
theorem weaklyHausdorff_of_isClosed {X : Type u} [TopologicalSpace X] [CompactlyGeneratedSpace X]
    (S : Setoid X)
    (hR : IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] {p : X × X | S p.1 p.2}) :
    CGWH.WeaklyHausdorffSpace (Quotient S) := by
  rw [isClosed_compactlyGenerated_iff] at hR
  have hq : IsQuotientMap (Quotient.mk S) := isQuotientMap_quotient_mk'
  -- Step 1: for every test map `h : L → X` the graph of `q ∘ h` is closed in `(X/S) × L`.
  have key : ∀ (L : Type u) [TopologicalSpace L] [CompactSpace L] [T2Space L] (h : L → X),
      Continuous h → IsClosed {p : Quotient S × L | p.1 = Quotient.mk S (h p.2)} := by
    intro L _ _ _ h hh
    have hπ : IsQuotientMap
        (fun p : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) => p.1.2 p.2) :=
      isQuotientMap_sigma
    have hqπ := hq.comp hπ
    -- the pulled back set on the disjoint union of the `T × L`
    have hF' : IsClosed {p : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst × L) |
        Quotient.mk S (p.1.2 p.2.1) = Quotient.mk S (h p.2.2)} := by
      rw [isClosed_sigma_iff]
      rintro ⟨T, c⟩
      have hc := hR (CompHaus.of (T × L))
        ⟨fun tl => (c tl.1, h tl.2),
          (c.continuous.comp continuous_fst).prodMk (hh.comp continuous_snd)⟩
      convert hc using 1
      ext tl
      exact Quotient.eq
    have hF : IsClosed {p : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) × L |
        Quotient.mk S (p.1.1.2 p.1.2) = Quotient.mk S (h p.2)} :=
      hF'.preimage (Homeomorph.sigmaProdDistrib (Y := L)).continuous
    rw [← isOpen_compl_iff, isOpen_iff_continuous_mem]
    refine hqπ.continuous_lift_prod_left ?_
    exact isOpen_iff_continuous_mem.mp hF.isOpen_compl
  -- Step 2: images of test maps are closed.
  refine ⟨fun K _ _ _ g hg => ?_⟩
  rw [← hq.isClosed_preimage]
  refine CompactlyGeneratedSpace.isClosed' fun L _ _ _ h hh => ?_
  have hC : IsClosed {p : L × K | g p.2 = Quotient.mk S (h p.1)} :=
    (key L h hh).preimage ((hg.comp continuous_snd).prodMk continuous_fst)
  have hpr := isClosedMap_fst_of_compactSpace (X := L) (Y := K) _ hC
  convert hpr using 1
  ext l
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨(l, k), hk, rfl⟩
  · rintro ⟨⟨l', k⟩, hk, rfl⟩
    exact ⟨k, hk⟩

end Sol_CGWH_weaklyHausdorffSpace_quotient_iff

open CGWH Sol_CGWH_weaklyHausdorffSpace_quotient_iff in
theorem solution
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedSpace X] (S : Setoid X) :
    WeaklyHausdorffSpace (Quotient S) ↔
      IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] {p : X × X | S p.1 p.2} := by
  constructor
  · intro hWH
    rw [isClosed_compactlyGenerated_iff]
    intro K f
    have h := isClosed_setOf_eq_of_weaklyHausdorff (Q := Quotient S) (K := K)
      (g₁ := fun k => Quotient.mk S (f k).1) (g₂ := fun k => Quotient.mk S (f k).2)
      (continuous_quotient_mk'.comp (continuous_fst.comp f.continuous))
      (continuous_quotient_mk'.comp (continuous_snd.comp f.continuous))
    convert h using 1
    ext k
    exact Quotient.eq.symm
  · exact weaklyHausdorff_of_isClosed S
