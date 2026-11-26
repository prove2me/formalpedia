-- Prove2me | solution 1 for C6BipartiteDomination.supportB_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:04.844138+00:00
-- url     : https://prove2.me/submissions/06084ae5-662e-461c-85c6-5444612ccdd1

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (w : V) :
    (supportB G D w).card = betaCharge G D w := by
  rfl
end C6BipartiteDomination
