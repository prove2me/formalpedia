-- Prove2me | solution 1 for C6BipartiteDomination.mem_responsibilityRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:40:41.073843+00:00
-- url     : https://prove2.me/submissions/ec4cb2b6-5e7e-4e71-b943-58d025cfc346

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D X : Finset V) (v : V) :
    v ∈ responsibilityRegion G D X ↔ Responsible G D X v := by
  classical
  simp [responsibilityRegion]
end C6BipartiteDomination
