-- Prove2me | solution 1 for C6BipartiteDomination.mem_PPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:26.92325+00:00
-- url     : https://prove2.me/submissions/60632820-a153-4ccf-8ff6-f2c4aa1dda81

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
    w ∈ PPart G D ↔ ∃ b ∈ BPart G D, w ∈ privateExternalNeighbors G D b := by
  classical
  simp [PPart]
end C6BipartiteDomination
