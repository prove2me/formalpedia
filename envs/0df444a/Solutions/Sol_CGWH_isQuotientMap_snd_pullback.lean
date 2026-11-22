-- Prove2me | solution 1 for CGWH.isQuotientMap_snd_pullback
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:12:52.797797+00:00
-- url     : https://prove2.me/submissions/79da31e1-1f0b-4bd1-82eb-346eaafa3d58

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_isQuotientMap_snd_pullback

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
    IsQuotientMap (fun p : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) => p.1.2 p.2) := by
  refine ⟨⟨?_⟩, fun x => ?_⟩
  · exact eq_compactlyGenerated
  · exact ⟨⟨⟨CompHaus.of PUnit.{u + 1}, ContinuousMap.const _ x⟩, PUnit.unit⟩, rfl⟩

/-- The core of the argument, over a compact Hausdorff base `K`: if `f : X → Y` is a quotient map
of a compactly generated space onto a weakly Hausdorff space, `g : T → Y` and `u : K → T` are
continuous and `A ⊆ T` has `k`-closed preimage in the fibre product of `f` and `g`, then the part
of the graph of `g ∘ u` lying over `u ⁻¹' A` is closed in `Y × K`. -/
theorem isClosed_graph_inter {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] [CompactlyGeneratedSpace X] [CGWH.WeaklyHausdorffSpace Y]
    {f : X → Y} (hf : IsQuotientMap f) {g : T → Y} (hg : Continuous g) {A : Set T}
    (hA : ∀ (S : CompHaus.{u}) (c : C(S, {p : X × T // f p.1 = g p.2})),
      IsClosed (c ⁻¹' ((fun p : {p : X × T // f p.1 = g p.2} => p.1.2) ⁻¹' A)))
    (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] {u : K → T}
    (hu : Continuous u) :
    IsClosed {p : Y × K | p.1 = g (u p.2) ∧ u p.2 ∈ A} := by
  have hπ : IsQuotientMap
      (fun p : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) => p.1.2 p.2) :=
    isQuotientMap_sigma
  have hfπ := hf.comp hπ
  -- the pulled back set on the disjoint union of the compact Hausdorff spaces `S × K`
  have hF' : IsClosed {p : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst × K) |
      f (p.1.2 p.2.1) = g (u p.2.2) ∧ u p.2.2 ∈ A} := by
    rw [isClosed_sigma_iff]
    rintro ⟨S, c⟩
    -- the coincidence set `E` of `f ∘ c` and `g ∘ u` on `S × K` is closed, hence compact Hausdorff
    have hE : IsClosed {sk : S × K | f (c sk.1) = g (u sk.2)} :=
      isClosed_setOf_eq_of_weaklyHausdorff (K := S × K) (Q := Y)
        (g₁ := fun sk => f (c sk.1)) (g₂ := fun sk => g (u sk.2))
        (hf.continuous.comp (c.continuous.comp continuous_fst))
        (hg.comp (hu.comp continuous_snd))
    have : CompactSpace {sk : S × K | f (c sk.1) = g (u sk.2)} :=
      isCompact_iff_compactSpace.mp hE.isCompact
    -- the test map `E → X ×_Y T`
    let φ : C({sk : S × K | f (c sk.1) = g (u sk.2)}, {p : X × T // f p.1 = g p.2}) :=
      ⟨fun e => ⟨(c e.1.1, u e.1.2), e.2⟩,
        Continuous.subtype_mk
          ((c.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
            (hu.comp (continuous_snd.comp continuous_subtype_val))) _⟩
    have hφ := hA (CompHaus.of {sk : S × K | f (c sk.1) = g (u sk.2)}) φ
    have himg := hE.isClosedEmbedding_subtypeVal.isClosedMap _ hφ
    convert himg using 1
    ext sk
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨sk, h1⟩, h2, rfl⟩
    · rintro ⟨⟨sk', h1⟩, h2, rfl⟩
      exact ⟨h1, h2⟩
  have hF : IsClosed {p : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) × K |
      f (p.1.1.2 p.1.2) = g (u p.2) ∧ u p.2 ∈ A} :=
    hF'.preimage (Homeomorph.sigmaProdDistrib (Y := K)).continuous
  -- Whitehead's lemma: `(f ∘ π) × id_K` is a quotient map since `K` is locally compact
  rw [← isOpen_compl_iff, isOpen_iff_continuous_mem]
  refine hfπ.continuous_lift_prod_left ?_
  exact isOpen_iff_continuous_mem.mp hF.isOpen_compl

end Sol_CGWH_isQuotientMap_snd_pullback

open CGWH Sol_CGWH_isQuotientMap_snd_pullback in
theorem solution
    {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
    [CompactlyGeneratedSpace T] [WeaklyHausdorffSpace T]
    {f : X → Y} (hf : IsQuotientMap f) {g : T → Y} (hg : Continuous g) :
    @IsQuotientMap {p : X × T // f p.1 = g p.2} T
      (TopologicalSpace.compactlyGenerated.{u} {p : X × T // f p.1 = g p.2}) _
      (fun p => p.1.2) := by
  refine (@isQuotientMap_iff_isClosed _ _ _
    (TopologicalSpace.compactlyGenerated.{u} {p : X × T // f p.1 = g p.2}) _).mpr
    ⟨fun t => ?_, fun A => ⟨fun hA => ?_, fun hA => ?_⟩⟩
  · -- surjectivity
    obtain ⟨x, hx⟩ := hf.surjective (g t)
    exact ⟨⟨(x, t), hx⟩, rfl⟩
  · -- continuity: the `k`-ification refines the subspace topology
    rw [isClosed_compactlyGenerated_iff]
    intro S c
    exact hA.preimage ((continuous_snd.comp continuous_subtype_val).comp c.continuous)
  · -- a set with `k`-closed preimage is closed
    rw [isClosed_compactlyGenerated_iff] at hA
    refine CompactlyGeneratedSpace.isClosed' fun K _ _ _ u hu => ?_
    have hΓ := isClosed_graph_inter hf hg hA K hu
    have hc : Continuous fun k : K => (g (u k), k) := (hg.comp hu).prodMk continuous_id
    have hpre := hΓ.preimage hc
    convert hpre using 1
    ext k
    constructor
    · intro hk
      exact ⟨rfl, hk⟩
    · rintro ⟨-, hk⟩
      exact hk
