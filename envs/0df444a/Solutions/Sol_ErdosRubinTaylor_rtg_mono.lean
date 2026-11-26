-- Prove2me | solution 1 for ErdosRubinTaylor.rtg_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:51.073321+00:00
-- url     : https://prove2.me/submissions/09e5e3c6-1035-4d1c-8eb7-609d7de7b544

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable {G : SimpleGraph V} {T T' : Set V}
namespace ErdosRubinTaylor
theorem _root_.solution (hTT : T ⊆ T') {u v : V} (h : Relation.ReflTransGen (adjIn G T) u v) :
    Relation.ReflTransGen (adjIn G T') u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hTT hbc.1, hTT hbc.2.1, hbc.2.2⟩
end ErdosRubinTaylor
