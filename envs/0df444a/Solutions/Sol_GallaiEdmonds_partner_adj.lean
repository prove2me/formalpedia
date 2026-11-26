-- Prove2me | solution 1 for GallaiEdmonds.partner_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:32.067014+00:00
-- url     : https://prove2.me/submissions/4bf5b82f-2263-4bc3-a282-b2e4fa87b29d

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
namespace GallaiEdmonds
theorem _root_.solution {M : G.Subgraph} (hM : M.IsMatching) {y : V} (hy : y ∈ M.verts) :
    M.Adj y (partner hM y) := by
  simp only [partner, hy, ↓reduceDIte]; exact (hM hy).choose_spec.1
end GallaiEdmonds
