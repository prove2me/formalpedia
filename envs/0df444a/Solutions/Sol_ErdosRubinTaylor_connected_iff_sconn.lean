-- Prove2me | solution 1 for ErdosRubinTaylor.connected_iff_sconn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:09.306261+00:00
-- url     : https://prove2.me/submissions/a30c3df9-d25b-4855-9f51-c14a426330f4

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
theorem _root_.solution : (G.induce T).Connected ↔ SConn G T := by
  constructor
  · intro hc
    obtain ⟨⟨v, hv⟩⟩ := hc.nonempty
    refine ⟨⟨v, hv⟩, fun u hu w hw => ?_⟩
    have key : ∀ (a b : T) (p : (G.induce T).Walk a b),
        Relation.ReflTransGen (adjIn G T) a.1 b.1 := by
      intro a b p
      induction p with
      | nil => exact Relation.ReflTransGen.refl
      | cons h _ ih => exact Relation.ReflTransGen.head ⟨Subtype.prop _, Subtype.prop _, h⟩ ih
    exact key ⟨u, hu⟩ ⟨w, hw⟩ (hc.preconnected ⟨u, hu⟩ ⟨w, hw⟩).some
  · rintro ⟨⟨a, ha⟩, h⟩
    have : Nonempty T := ⟨⟨a, ha⟩⟩
    refine Connected.mk ?_
    rintro ⟨u, hu⟩ ⟨w, hw⟩
    have key : ∀ x y, Relation.ReflTransGen (adjIn G T) x y → ∀ (hx : x ∈ T) (hy : y ∈ T),
        (G.induce T).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
      intro x y hxy
      induction hxy with
      | refl => intro _ _; exact Reachable.refl _
      | tail _ hbc ih =>
        intro hx hy
        refine (ih hx hbc.1).trans (Adj.reachable ?_)
        exact hbc.2.2
    exact key u w (h u hu w hw) hu hw
end ErdosRubinTaylor
