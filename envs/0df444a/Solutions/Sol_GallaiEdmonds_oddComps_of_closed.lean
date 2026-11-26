-- Prove2me | solution 1 for GallaiEdmonds.oddComps_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:04.541232+00:00
-- url     : https://prove2.me/submissions/6ba90de2-1605-42a5-abff-89af8d578f7b

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_comps_of_closed

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution (hW : W' ⊆ W) (hc : Closed G W W') :
    oddComps G W' = {K | K ∈ oddComps G W ∧ K ⊆ W'} := by
  ext K
  simp only [oddComps, comps_of_closed hW hc, Set.mem_ofPred_eq]
  tauto
end GallaiEdmonds
