-- Prove2me | solution 1 for C6BipartiteDomination.ZPart_disjoint_BPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:50.028696+00:00
-- url     : https://prove2.me/submissions/cd198cd9-8f67-479d-9dbe-d4a4957a50c3

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
import Theorems.Thm_C6BipartiteDomination_mem_BPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) :
    Disjoint (ZPart G D) (BPart G D) := by
  rw [Finset.disjoint_left]
  intro z hz hb
  exact (mem_BPart G D z).mp hb |>.2 hz
end C6BipartiteDomination
