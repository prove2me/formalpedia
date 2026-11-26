-- Prove2me | solution 1 for C6BipartiteDomination.selected_Z_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:44.015497+00:00
-- url     : https://prove2.me/submissions/87537587-b246-4d6c-8eb4-5ba4a2c42acf

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_mem_ZPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V} {z v : V}
    (hz : z ∈ ZPart G D) (hv : v ∈ D) : ¬ G.Adj z v :=
  (mem_ZPart G D z).mp hz |>.2 v hv
end C6BipartiteDomination
