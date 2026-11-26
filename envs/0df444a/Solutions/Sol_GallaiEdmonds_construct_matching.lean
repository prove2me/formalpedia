-- Prove2me | solution 1 for GallaiEdmonds.construct_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:58.150681+00:00
-- url     : https://prove2.me/submissions/d17255fd-0f69-4e06-98c5-30ca302ae47f

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Theorems.Thm_GallaiEdmonds_cc_mem_comps
public import Theorems.Thm_GallaiEdmonds_comps_eq_of_mem
public import Theorems.Thm_GallaiEdmonds_comps_nonempty
public import Theorems.Thm_GallaiEdmonds_comps_subset
public import Theorems.Thm_GallaiEdmonds_mem_cc_self


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} {v : V} (hv : v ∈ oddPart G U)
    {f : V → Set V}
    (hf : ∀ u ∈ U, f u ∈ oddComps G Uᶜ ∧ f u ≠ cc G Uᶜ v ∧ ∃ x ∈ f u, G.Adj u x)
    (hfinj : Set.InjOn f U)
    (hfc : ∀ K ∈ oddComps G Uᶜ, ∀ y ∈ K, ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K \ {y})
    (hev : ∀ K ∈ comps G Uᶜ, Even K.ncard → ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧ v ∉ M'.verts ∧
      M'.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard := by
  classical
  have : Nonempty V := ⟨v⟩
  set K0 := cc G Uᶜ v with hK0
  have hK0c : K0 ∈ oddComps G Uᶜ := ⟨cc_mem_comps hv.1, hv.2⟩
  choose! x hxf hxadj using fun u (hu : u ∈ U) => (hf u hu).2.2
  have hxU : ∀ u ∈ U, x u ∉ U := fun u hu => comps_subset (hf u hu).1.1 (hxf u hu)
  have hexe : ∀ K ∈ oddComps G Uᶜ,
      ∃ y ∈ K, (∀ u ∈ U, f u = K → y = x u) ∧ (K = K0 → y = v) := by
    intro K hK
    by_cases h : ∃ u ∈ U, f u = K
    · obtain ⟨u, hu, rfl⟩ := h
      exact ⟨x u, hxf u hu, fun u' hu' h' => by rw [hfinj hu' hu h'],
        fun h' => ((hf u hu).2.1 h').elim⟩
    · push Not at h
      by_cases h0 : K = K0
      · exact ⟨v, h0 ▸ mem_cc_self hv.1, fun u hu h' => (h u hu h').elim, fun _ => rfl⟩
      · obtain ⟨y, hy⟩ := comps_nonempty hK.1
        exact ⟨y, hy, fun u hu h' => (h u hu h').elim, fun h' => (h0 h').elim⟩
  choose! e he heU heK0 using hexe
  let hole : Set V → Set V := fun K => {y | Odd K.ncard ∧ y = e K}
  have hexP : ∀ K ∈ comps G Uᶜ, ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K \ hole K := by
    intro K hK
    by_cases hodd : Odd K.ncard
    · obtain ⟨P, hP, hPv⟩ := hfc K ⟨hK, hodd⟩ (e K) (he K ⟨hK, hodd⟩)
      refine ⟨P, hP, ?_⟩
      rw [hPv]
      congr 1
      ext y
      simp [hole, hodd]
    · obtain ⟨P, hP, hPv⟩ := hev K hK (Nat.not_odd_iff_even.mp hodd)
      refine ⟨P, hP, ?_⟩
      rw [hPv]
      ext y
      simp [hole, hodd]
  choose! P hP hPv using hexP
  let E1 : U → G.Subgraph := fun u => G.subgraphOfAdj (hxadj u.1 u.2)
  let E2 : comps G Uᶜ → G.Subgraph := fun K => P K.1
  have hE1m : ∀ u, (E1 u).IsMatching := fun u => Subgraph.IsMatching.subgraphOfAdj _
  have hE2m : ∀ K, (E2 K).IsMatching := fun K => hP K.1 K.2
  have hE1v : ∀ u, (E1 u).verts = {u.1, x u.1} := fun u => rfl
  have hE2v : ∀ K, (E2 K).verts = K.1 \ hole K.1 := fun K => hPv K.1 K.2
  have hE1d : Pairwise fun i j => Disjoint (E1 i).support (E1 j).support := by
    intro i j hij
    rw [(hE1m i).support_eq_verts, (hE1m j).support_eq_verts, hE1v, hE1v, Set.disjoint_left]
    intro y hyi hyj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyi hyj
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have hfne : f i.1 ≠ f j.1 := fun h => hne (hfinj i.2 j.2 h)
    rcases hyi with rfl | rfl <;> rcases hyj with h | h
    · exact hne h
    · exact hxU j.1 j.2 (h ▸ i.2)
    · exact hxU i.1 i.2 (h ▸ j.2)
    · exact hfne (comps_eq_of_mem (hf i.1 i.2).1.1 (hf j.1 j.2).1.1 (hxf i.1 i.2)
        (h ▸ hxf j.1 j.2))
  have hE2d : Pairwise fun i j => Disjoint (E2 i).support (E2 j).support := by
    intro i j hij
    rw [(hE2m i).support_eq_verts, (hE2m j).support_eq_verts, hE2v, hE2v, Set.disjoint_left]
    intro y hyi hyj
    exact hij (Subtype.ext (comps_eq_of_mem i.2 j.2 hyi.1 hyj.1))
  have hM1 := Subgraph.IsMatching.iSup hE1m hE1d
  have hM2 := Subgraph.IsMatching.iSup hE2m hE2d
  have hmem1 : ∀ y, y ∈ (⨆ u, E1 u).verts ↔ ∃ u ∈ U, y = u ∨ y = x u := by
    intro y
    simp only [Subgraph.verts_iSup, Set.mem_iUnion, hE1v, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, h⟩; exact ⟨u.1, u.2, h⟩
    · rintro ⟨u, hu, h⟩; exact ⟨⟨u, hu⟩, h⟩
  have hmem2 : ∀ y, y ∈ (⨆ K, E2 K).verts ↔ ∃ K ∈ comps G Uᶜ, y ∈ K ∧ y ∉ hole K := by
    intro y
    simp only [Subgraph.verts_iSup, Set.mem_iUnion, hE2v, Set.mem_sdiff]
    constructor
    · rintro ⟨K, h⟩; exact ⟨K.1, K.2, h⟩
    · rintro ⟨K, hK, h⟩; exact ⟨⟨K, hK⟩, h⟩
  have hd : Disjoint (⨆ u, E1 u).support (⨆ K, E2 K).support := by
    rw [hM1.support_eq_verts, hM2.support_eq_verts, Set.disjoint_left]
    intro y hy1 hy2
    obtain ⟨u, hu, hyu⟩ := (hmem1 y).1 hy1
    obtain ⟨K, hK, hyK, hyh⟩ := (hmem2 y).1 hy2
    rcases hyu with rfl | rfl
    · exact comps_subset hK hyK hu
    · have hKf : f u = K := comps_eq_of_mem (hf u hu).1.1 hK (hxf u hu) hyK
      apply hyh
      refine ⟨hKf ▸ (hf u hu).1.2, ?_⟩
      exact (heU K (hKf ▸ (hf u hu).1) u hu hKf).symm
  let M' := (⨆ u, E1 u) ⊔ (⨆ K, E2 K)
  have hM' : M'.IsMatching := hM1.sup hM2 hd
  have hmem : ∀ y, y ∈ M'.verts ↔
      (∃ u ∈ U, y = u ∨ y = x u) ∨ (∃ K ∈ comps G Uᶜ, y ∈ K ∧ y ∉ hole K) := by
    intro y
    rw [Subgraph.verts_sup, Set.mem_union, hmem1, hmem2]
  set E := e '' (oddComps G Uᶜ \ f '' U) with hE
  have hnot : ∀ y, y ∉ M'.verts ↔ y ∈ E := by
    intro y
    rw [hmem]
    constructor
    · intro h
      push Not at h
      obtain ⟨h1, h2⟩ := h
      have hyU : y ∈ Uᶜ := fun hyU => (h1 y hyU).1 rfl
      have hK := cc_mem_comps (G := G) hyU
      have hyK : y ∈ cc G Uᶜ y := mem_cc_self hyU
      have hhole := h2 _ hK hyK
      refine ⟨cc G Uᶜ y, ⟨⟨hK, hhole.1⟩, ?_⟩, hhole.2.symm⟩
      rintro ⟨u, hu, hfu⟩
      exact (h1 u hu).2 (hhole.2.trans (heU _ ⟨hK, hhole.1⟩ u hu hfu))
    · rintro ⟨K, ⟨hK, hKf⟩, rfl⟩ h
      rcases h with ⟨u, hu, h | h⟩ | ⟨K', hK', hyK', hyh⟩
      · exact comps_subset hK.1 (he K hK) (h ▸ hu)
      · exact hKf ⟨u, hu, comps_eq_of_mem (hf u hu).1.1 hK.1 (hxf u hu) (h ▸ he K hK)⟩
      · have : K' = K := comps_eq_of_mem hK' hK.1 hyK' (he K hK)
        subst this
        exact hyh ⟨hK.2, rfl⟩
  refine ⟨M', hM', ?_, ?_⟩
  · rw [hnot]
    refine ⟨K0, ⟨hK0c, ?_⟩, heK0 K0 hK0c rfl⟩
    rintro ⟨u, hu, hfu⟩
    exact (hf u hu).2.1 hfu
  · have hcompl : M'.vertsᶜ = E := Set.ext hnot
    have h1 := Set.ncard_add_ncard_compl M'.verts
    have heinj : Set.InjOn e (oddComps G Uᶜ \ f '' U) := by
      intro K hK K' hK' h
      exact comps_eq_of_mem hK.1.1 hK'.1.1 (he K hK.1) (h ▸ he K' hK'.1)
    have h2 : E.ncard = (oddComps G Uᶜ \ f '' U).ncard := heinj.ncard_image
    have hfU : f '' U ⊆ oddComps G Uᶜ := by
      rintro _ ⟨u, hu, rfl⟩; exact (hf u hu).1
    have h3 := Set.ncard_sdiff_add_ncard_of_subset hfU
    have h4 : (f '' U).ncard = U.ncard := hfinj.ncard_image
    rw [hcompl] at h1
    unfold oddC
    omega
end GallaiEdmonds
