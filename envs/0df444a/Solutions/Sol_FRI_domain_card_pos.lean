-- Prove2me | solution 1 for FRI_domain_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:07:34.850103+00:00
-- url     : https://prove2.me/submissions/facd42ae-2f8c-4881-8c09-37afa8e5155a

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_D0_card_pos

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (i : Fin (P.num_foldings + 1)) :
    0 < (FRI_domain P i).card := by
  induction i using Fin.induction with
  | zero => exact FRI_D0_card_pos P
  | succ i ih =>
    have h_domain_eq := FRI_domain_succ_eq P i i.isLt
    simpa only [Fin.val_succ, Fin.val_castSucc, h_domain_eq, pow_domain, Finset.card_pos] using
      (Finset.card_pos.mp ih).image (· ^ P.m ⟨i, i.isLt⟩)
