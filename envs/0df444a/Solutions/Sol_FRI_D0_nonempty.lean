-- Prove2me | solution 1 for FRI_D0_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:57:24.497542+00:00
-- url     : https://prove2.me/submissions/8e79da99-845b-4de1-b43e-110a8f762cc7

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) : P.D_0.Nonempty := by
  apply Finset.card_pos.1
  have := P.h_d0_le_D0
  have := P.h_d0_pos
  grind
