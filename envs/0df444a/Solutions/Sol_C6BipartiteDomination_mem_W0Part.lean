-- Prove2me | solution 1 for C6BipartiteDomination.mem_W0Part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:47.955423+00:00
-- url     : https://prove2.me/submissions/5efd1a6c-8d49-42f3-8f6e-f47269bc6516

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (w : V) :
    w ∈ W0Part G D ↔ w ∉ D ∧ ∀ b ∈ BPart G D, ¬ G.Adj b w := by
  classical
  simp [W0Part]
end C6BipartiteDomination
