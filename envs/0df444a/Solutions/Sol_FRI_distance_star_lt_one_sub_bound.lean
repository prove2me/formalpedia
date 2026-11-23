-- Prove2me | solution 1 for FRI_distance_star_lt_one_sub_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:42:50.662441+00:00
-- url     : https://prove2.me/submissions/98b29a0d-9247-4de0-b6a8-a80bff048d5b

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Theorems.Thm_FRI_D0_card_pos


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) :
    FRI_distance_star P f_0 bound < 1 - bound := by
  unfold FRI_distance_star
  have h_eps : 1 / (P.D_0.card : ℝ) > 0 :=
    one_div_pos.mpr (Nat.cast_pos.mpr (FRI_D0_card_pos P))
  grind
