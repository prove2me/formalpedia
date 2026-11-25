-- Prove2me | solution 1 for CommonCycle.exists_cycle_through_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:05:34.983619+00:00
-- url     : https://prove2.me/submissions/c514b67c-2a00-4f7c-9074-d390de554c65

module
public import Mathlib
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Definitions.Def_DiracCommonCycle_Solution
public import Theorems.Thm_DiracCycle_exists_cycle_through_pair


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open CommonCycle
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace CommonCycle
theorem _root_.solution (hn : 2 < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < 2 → (G.induce Sᶜ).Connected) (a b : V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ a ∈ c.support ∧ b ∈ c.support :=
  DiracCycle.exists_cycle_through_pair G hn hconn a b
end CommonCycle
