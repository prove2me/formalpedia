-- Prove2me | solution 1 for C6BipartiteDomination.responsible_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:40:27.545563+00:00
-- url     : https://prove2.me/submissions/7cf83c59-505f-4696-9ba5-c4a4b3f660c1

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic
import Definitions.Def_C6BipartiteDomination_Basic

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    (D X : Finset V) (v : V) :
    Responsible G D X v ↔ v ∉ D \ X ∧ ∀ u ∈ D \ X, ¬ G.Adj u v := Iff.rfl
end C6BipartiteDomination
