-- Prove2me | solution 1 for DiracCycle.exists_cycle_through_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:02:35.308915+00:00
-- url     : https://prove2.me/submissions/9f7e7fce-6710-40ee-9294-4b75daa9a1a5

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Theorems.Thm_DiracCycle_exists_cycle_through

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace DiracCycle
theorem _root_.solution (hn : 2 < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < 2 → (G.induce Sᶜ).Connected) (a b : V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ a ∈ c.support ∧ b ∈ c.support := by
  classical
  obtain ⟨v, c, hc, hab⟩ := exists_cycle_through G le_rfl hn hconn {a, b} Finset.card_le_two
  exact ⟨v, c, hc, hab a (by simp), hab b (by simp)⟩
end DiracCycle
