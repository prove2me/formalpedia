-- Prove2me | solution 1 for C6BipartiteDomination.neighbor_of_independent_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:41:45.010701+00:00
-- url     : https://prove2.me/submissions/ba72b1e5-71f0-4ce5-9488-90601101252b

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V} (hD : Independent G D)
    {u v : V} (hu : u ∈ D) (hadj : G.Adj u v) : v ∉ D := by
  intro hv
  exact hD hu hv hadj
end C6BipartiteDomination
