-- Prove2me | solution 1 for GallaiEdmonds.ncard_verts_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:14.213568+00:00
-- url     : https://prove2.me/submissions/957d2b28-7845-4b8d-a716-624e6240bd80

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
open Finset
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have h := M.spanningCoe.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
    intro v
    rw [Subgraph.degree_spanningCoe]
    split_ifs with hv
    · exact (Subgraph.isMatching_iff_forall_degree.1 hM) v hv
    · exact Subgraph.degree_of_notMem_verts hv
  simp only [hdeg, Finset.sum_boole, Nat.cast_id] at h
  have e1 : M.verts.ncard = #{x | x ∈ M.verts} := by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  have e2 : M.edgeSet.ncard = #M.spanningCoe.edgeFinset := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset, Subgraph.edgeSet_spanningCoe]
  rw [e1, e2, h]
end GallaiEdmonds
