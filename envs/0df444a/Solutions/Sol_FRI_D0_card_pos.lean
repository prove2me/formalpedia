-- Prove2me | solution 1 for FRI_D0_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:01:25.286074+00:00
-- url     : https://prove2.me/submissions/f86b7473-6b53-42a5-b917-63f39850616b

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_D0_nonempty

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) :
    0 < (FRI_domain P 0).card :=
  Finset.card_pos.mpr (FRI_D0_nonempty P)
