-- Prove2me | solution 1 for CommonCycle.exists_cycle_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:03:37.518541+00:00
-- url     : https://prove2.me/submissions/30816a2b-8b16-48af-807f-9ac80bb22d63

module
public import Mathlib
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Definitions.Def_DiracCommonCycle_Solution
public import Theorems.Thm_DiracCycle_exists_cycle_through


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open CommonCycle
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace CommonCycle
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) (hn : k < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) (S : Finset V)
    (hS : #S ≤ k) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∀ x ∈ S, x ∈ c.support :=
  DiracCycle.exists_cycle_through G hk hn hconn S hS
end CommonCycle
