-- Prove2me | solution 1 for ErdosRubinTaylor.rtg_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:02.366011+00:00
-- url     : https://prove2.me/submissions/18643491-b697-484a-bb2a-65b1fe339dc0

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
theorem _root_.solution {W D : Set V}
    (hcl : ∀ u ∈ D, ∀ v ∈ W, G.Adj u v → v ∈ D) {u v : V}
    (h : Relation.ReflTransGen (adjIn G W) u v) (hu : u ∈ D) :
    Relation.ReflTransGen (adjIn G D) u v ∧ v ∈ D := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hu⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hc := hcl _ ih2 _ hbc.2.1 hbc.2.2
    exact ⟨ih1.tail ⟨ih2, hc, hbc.2.2⟩, hc⟩
end ErdosRubinTaylor
