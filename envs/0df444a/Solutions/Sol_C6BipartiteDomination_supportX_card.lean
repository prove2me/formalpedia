-- Prove2me | solution 1 for C6BipartiteDomination.supportX_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:46:52.789092+00:00
-- url     : https://prove2.me/submissions/585241fa-38ea-47a9-923b-300951a57687

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) (w : V) :
    (supportX G D w).card = kCharge G D w := by
  classical
  simp [supportX, kCharge, degreeTo, G.adj_comm]
end C6BipartiteDomination
