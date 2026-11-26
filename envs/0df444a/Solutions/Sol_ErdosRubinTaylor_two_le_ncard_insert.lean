-- Prove2me | solution 1 for ErdosRubinTaylor.two_le_ncard_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:39:09.604487+00:00
-- url     : https://prove2.me/submissions/909aef87-9013-4928-972c-c25a1632b65d

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
namespace ErdosRubinTaylor
theorem _root_.solution [Finite V] {D : Set V} {x b : V} (hb : b ∈ D) (hxb : x ≠ b) :
    2 ≤ (insert x D).ncard := by
  have hsub : ({x, b} : Set V) ⊆ insert x D := Set.insert_subset_insert (by simpa using hb)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_pair hxb] at this
end ErdosRubinTaylor
