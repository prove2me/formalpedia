-- Prove2me | solution 1 for C6BipartiteDomination.mem_BPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:47.393898+00:00
-- url     : https://prove2.me/submissions/44f9d551-2742-4364-a1b4-1df249f09d01

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (b : V) :
    b ∈ BPart G D ↔ b ∈ D ∧ b ∉ ZPart G D := by
  simp [BPart, Finset.mem_sdiff]
end C6BipartiteDomination
