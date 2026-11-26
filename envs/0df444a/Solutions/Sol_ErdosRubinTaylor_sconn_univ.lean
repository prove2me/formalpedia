-- Prove2me | solution 1 for ErdosRubinTaylor.sconn_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:35:15.297729+00:00
-- url     : https://prove2.me/submissions/443ece46-9ace-41b7-bef5-b542157968b2

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
theorem _root_.solution (hconn : G.Connected) : SConn G Set.univ := by
  obtain ⟨v⟩ := hconn.nonempty
  refine ⟨⟨v, trivial⟩, fun u _ w _ => ?_⟩
  have key : ∀ (a b : V) (p : G.Walk a b), Relation.ReflTransGen (adjIn G Set.univ) a b := by
    intro a b p
    induction p with
    | nil => exact Relation.ReflTransGen.refl
    | cons h _ ih => exact Relation.ReflTransGen.head ⟨trivial, trivial, h⟩ ih
  exact key u w (hconn.preconnected u w).some
end ErdosRubinTaylor
