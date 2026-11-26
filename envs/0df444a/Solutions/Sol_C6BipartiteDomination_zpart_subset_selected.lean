-- Prove2me | solution 1 for C6BipartiteDomination.zpart_subset_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:12.730693+00:00
-- url     : https://prove2.me/submissions/67e447b4-e431-45b6-a1b2-2f519ca50320

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
import Theorems.Thm_C6BipartiteDomination_mem_ZPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) : ZPart G D ⊆ D := by
  intro z hz
  exact (mem_ZPart G D z).mp hz |>.1
end C6BipartiteDomination
