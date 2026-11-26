-- Prove2me | solution 1 for GallaiEdmonds.partner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:40.252966+00:00
-- url     : https://prove2.me/submissions/1aa62496-af05-44bb-8336-feacf8c87b9c

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Theorems.Thm_GallaiEdmonds_partner_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution {M : G.Subgraph} (hM : M.IsMatching) {y w : V} (h : M.Adj y w) :
    partner hM y = w :=
  hM.eq_of_adj_left (partner_adj hM (M.edge_vert h)) h
end GallaiEdmonds
