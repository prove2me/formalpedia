-- Prove2me | solution 1 for GallaiEdmonds.minBarrier_factorCritical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:08:44.159695+00:00
-- url     : https://prove2.me/submissions/8713b5e3-147e-4cb7-94f0-a7030dcaee16

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_isBarrier_of_le
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_closed
public import Theorems.Thm_GallaiEdmonds_closed_compl
public import Theorems.Thm_GallaiEdmonds_comps_closed
public import Theorems.Thm_GallaiEdmonds_comps_eq_cc
public import Theorems.Thm_GallaiEdmonds_comps_subset
public import Theorems.Thm_GallaiEdmonds_even_ncard_verts
public import Theorems.Thm_GallaiEdmonds_oddC_split
public import Theorems.Thm_GallaiEdmonds_oddComps_self
public import Theorems.Thm_GallaiEdmonds_tb_restricted


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    {M : G.Subgraph} (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    {K : Set V} (hK : K ∈ oddComps G Uᶜ) {v : V} (hv : v ∈ K) :
    ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K \ {v} := by
  by_contra hno
  push Not at hno
  set S := K \ {v} with hS
  obtain ⟨N, hN, hNS, T, hTS, hineq⟩ := tb_restricted G S
  have hNne : N.verts ≠ S := hno N hN
  have hlt : N.verts.ncard < S.ncard :=
    Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hNS, hNne⟩)
  have hSK : S.ncard + 1 = K.ncard := Set.ncard_sdiff_singleton_add_one hv
  have hev := even_ncard_verts hN
  have hodd := hK.2
  have hlt2 : N.verts.ncard + 2 ≤ S.ncard := by
    obtain ⟨a, ha⟩ := hev; obtain ⟨b, hb⟩ := hodd; omega
  set U' := U ∪ insert v T with hU'
  have hvU : v ∉ U := comps_subset hK.1 hv
  have hTK : T ⊆ K := fun t ht => (hTS ht).1
  have hTv : v ∉ T := fun h => (hTS h).2 rfl
  have hTU : Disjoint U (insert v T) := by
    rw [Set.disjoint_left]
    intro x hxU hx
    rcases hx with rfl | hx
    · exact hvU hxU
    · exact comps_subset hK.1 (hTK hx) hxU
  have hcardU' : U'.ncard = U.ncard + T.ncard + 1 := by
    rw [hU', Set.ncard_union_eq hTU, Set.ncard_insert_of_notMem hTv]
    ring
  have hsub1 : S \ T ⊆ U'ᶜ := by
    intro x hx
    simp only [hU', Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff, not_or]
    exact ⟨comps_subset hK.1 hx.1.1, hx.1.2, hx.2⟩
  have hcl1 : Closed G U'ᶜ (S \ T) := by
    intro y hy z hz hadj
    simp only [hU', Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff, not_or] at hz
    exact ⟨⟨comps_closed hK.1 y hy.1.1 z hz.1 hadj, hz.2.1⟩, hz.2.2⟩
  have hrest : U'ᶜ \ (S \ T) = Uᶜ \ K := by
    ext x
    simp only [hU', hS, Set.mem_sdiff, Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨⟨hxU, hxv, hxT⟩, h⟩
      exact ⟨hxU, fun hxK => h ⟨⟨hxK, hxv⟩, hxT⟩⟩
    · rintro ⟨hxU, hxK⟩
      exact ⟨⟨hxU, fun h => hxK (h ▸ hv), fun h => hxK (hTK h)⟩, fun h => hxK h.1.1⟩
  have hsplit1 := oddC_split hsub1 hcl1
  rw [hrest] at hsplit1
  have hsplit2 := oddC_split (comps_subset hK.1) (comps_closed hK.1)
  have hK1 : oddC G K = 1 := by rw [oddC, oddComps_self hK.1 hK.2, Set.ncard_singleton]
  have heq := hU.1.eq hM hmax
  have hU'bar : IsBarrier G U' := isBarrier_of_le hM (by omega)
  have hsubOP : oddPart G U' ⊆ oddPart G U \ {v} := by
    rintro y ⟨hyU', hyodd⟩
    by_cases hyST : y ∈ S \ T
    · refine ⟨⟨comps_subset hK.1 hyST.1.1, ?_⟩, hyST.1.2⟩
      rw [← comps_eq_cc hK.1 hyST.1.1]
      exact hK.2
    · have hy0 : y ∈ U'ᶜ \ (S \ T) := ⟨hyU', hyST⟩
      have hy1 : y ∈ Uᶜ \ K := hrest ▸ hy0
      have e1 : cc G (U'ᶜ \ (S \ T)) y = cc G U'ᶜ y :=
        cc_eq_of_closed Set.sdiff_subset (closed_compl hcl1) hy0
      have e2 : cc G (Uᶜ \ K) y = cc G Uᶜ y :=
        cc_eq_of_closed Set.sdiff_subset (closed_compl (comps_closed hK.1)) hy1
      rw [hrest] at e1
      refine ⟨⟨hy1.1, ?_⟩, ?_⟩
      · rw [← e2, e1]; exact hyodd
      · rintro rfl; exact hy1.2 hv
  have hvOP : v ∈ oddPart G U := ⟨hvU, by rw [← comps_eq_cc hK.1 hv]; exact hK.2⟩
  have h1 := Set.ncard_le_ncard hsubOP
  have h2 : (oddPart G U \ {v}).ncard < (oddPart G U).ncard :=
    Set.ncard_sdiff_singleton_lt_of_mem hvOP
  have h3 := hU.2 U' hU'bar
  omega
end GallaiEdmonds
