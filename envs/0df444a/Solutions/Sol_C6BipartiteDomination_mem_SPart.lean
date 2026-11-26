-- Prove2me | solution 1 for C6BipartiteDomination.mem_SPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:46.739429+00:00
-- url     : https://prove2.me/submissions/4751587f-d9bc-4b77-afde-0a4f3e74fca5

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
    w ∈ SPart G D ↔ w ∈ WBPart G D ∧ w ∉ PPart G D := by
  simp [SPart, Finset.mem_sdiff]
end C6BipartiteDomination
