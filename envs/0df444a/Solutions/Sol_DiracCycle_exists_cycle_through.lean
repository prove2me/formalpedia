-- Prove2me | solution 1 for DiracCycle.exists_cycle_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:00:37.809803+00:00
-- url     : https://prove2.me/submissions/8a2e896b-113d-4d72-9090-9be11f06f534

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Theorems.Thm_DiracCycle_exists_isCycle_support
public import Theorems.Thm_DiracCycle_exists_cycArr_through

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace DiracCycle
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) (hn : k < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) (S : Finset V)
    (hS : #S ≤ k) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∀ x ∈ S, x ∈ c.support := by
  obtain ⟨m, f, hC, hSC⟩ := exists_cycArr_through hk hn hconn S hS
  obtain ⟨c, hc, hsup⟩ := exists_isCycle_support hC
  refine ⟨f 0, c, hc, fun x hx => ?_⟩
  obtain ⟨i, rfl⟩ := hSC x hx
  exact hsup i
end DiracCycle
