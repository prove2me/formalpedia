-- Prove2me | solution 1 for GallaiEdmonds.oddC_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:05:10.37086+00:00
-- url     : https://prove2.me/submissions/531b0f1e-87e2-44ae-b27f-2f2cbce126b5

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_cc_subset
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_closed
public import Theorems.Thm_GallaiEdmonds_comps_subset
public import Theorems.Thm_GallaiEdmonds_comps_nonempty
public import Theorems.Thm_GallaiEdmonds_comps_eq_cc
public import Theorems.Thm_GallaiEdmonds_oddComps_of_closed
public import Theorems.Thm_GallaiEdmonds_closed_compl

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] (hW : W' ⊆ W) (hc : Closed G W W') :
    oddC G W = oddC G W' + oddC G (W \ W') := by
  have h1 := oddComps_of_closed hW hc
  have h2 := oddComps_of_closed (Set.sdiff_subset) (closed_compl hc)
  have hU : oddComps G W = oddComps G W' ∪ oddComps G (W \ W') := by
    rw [h1, h2]
    ext K
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hK
      obtain ⟨y, hy⟩ := comps_nonempty hK.1
      by_cases hyW' : y ∈ W'
      · left
        refine ⟨hK, ?_⟩
        rw [comps_eq_cc hK.1 hy, ← cc_eq_of_closed hW hc hyW']
        exact cc_subset
      · right
        refine ⟨hK, ?_⟩
        have hyd : y ∈ W \ W' := ⟨comps_subset hK.1 hy, hyW'⟩
        rw [comps_eq_cc hK.1 hy, ← cc_eq_of_closed Set.sdiff_subset (closed_compl hc) hyd]
        exact cc_subset
    · rintro (h | h) <;> exact h.1
  have hD : Disjoint (oddComps G W') (oddComps G (W \ W')) := by
    rw [Set.disjoint_left]
    intro K hK hK'
    obtain ⟨y, hy⟩ := comps_nonempty hK.1
    exact (comps_subset hK'.1 hy).2 (comps_subset hK.1 hy)
  unfold oddC
  rw [hU, Set.ncard_union_eq hD (Set.toFinite _) (Set.toFinite _)]
end GallaiEdmonds
