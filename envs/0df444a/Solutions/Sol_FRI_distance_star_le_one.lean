-- Prove2me | solution 1 for FRI_distance_star_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:41:46.672083+00:00
-- url     : https://prove2.me/submissions/40f3ed04-813e-45d7-9142-2c425ed39004

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_D0_card_pos

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) :
    FRI_distance_star P f_0 bound ≤ 1 := by
  unfold FRI_distance_star
  refine (min_le_left ..).trans ?_
  -- Show relDistanceToSet ≤ 1 since relDistance is hammingDist / card
  unfold relDistanceToSet
  have h_zero_in_code := Submodule.zero_mem (FRI_code P 0)
  refine csInf_le_of_le ⟨0, fun d ⟨g, _, hd⟩ ↦ hd ▸ by unfold relDistance; positivity⟩
    ⟨0, h_zero_in_code, rfl⟩ ?_
  unfold relDistance
  rw [div_le_one (by simp only [Fintype.card_coe]; exact Nat.cast_pos.mpr (FRI_D0_card_pos P))]
  exact_mod_cast hammingDist_le_card_fintype
