-- Prove2me | solution 1 for FirstPassageLinearTransport.card_badTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:01.42209+00:00
-- url     : https://prove2.me/submissions/09fe716c-e2a4-40a9-9522-7a696b5c4e42

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (S : Set ℕ) (Y : ℕ) :
    (badTarget S Y).card = badCount S Y := by
  rfl
end FirstPassageLinearTransport
