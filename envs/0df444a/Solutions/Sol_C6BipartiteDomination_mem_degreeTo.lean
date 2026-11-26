-- Prove2me | solution 1 for C6BipartiteDomination.mem_degreeTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:11.251817+00:00
-- url     : https://prove2.me/submissions/0ee40acd-28ee-4bfb-9ee2-e135d3bc3c78

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
open Classical
namespace C6BipartiteDomination
theorem _root_.solution (A : Finset V) (v u : V) :
    u ∈ A.filter (fun x => G.Adj v x) ↔ u ∈ A ∧ G.Adj v u := by
  simp
end C6BipartiteDomination
