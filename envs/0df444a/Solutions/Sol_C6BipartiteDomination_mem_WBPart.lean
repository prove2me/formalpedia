-- Prove2me | solution 1 for C6BipartiteDomination.mem_WBPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:46.033968+00:00
-- url     : https://prove2.me/submissions/adbd1606-bccc-42f4-b571-40eddff4d809

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (w : V) :
    w ∈ WBPart G D ↔ w ∉ D ∧ w ∉ W0Part G D := by
  simp [WBPart, Finset.mem_sdiff]
end C6BipartiteDomination
