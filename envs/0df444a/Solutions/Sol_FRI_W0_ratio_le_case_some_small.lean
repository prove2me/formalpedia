-- Prove2me | solution 1 for FRI_W0_ratio_le_case_some_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:36:23.760115+00:00
-- url     : https://prove2.me/submissions/be05d6b8-11e2-403a-aa00-0c895043cc0c

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_claim_queryphase_if_domain_small


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_domain_size : FRI_Domain_Size_Property P)
    (h_D_pos : ∀ i : Fin (P.num_foldings + 1), (FRI_domain P i).card > 0)
    (i_star : Fin (P.num_foldings + 1))
    (h_small : (FRI_W P f_0 T i_star).card <
      (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i_star).card) :
    ((FRI_W P f_0 T 0).card : ℝ) / (FRI_domain P 0).card ≤ 1 - FRI_distance_star P f_0 bound := by
  have := FRI_claim_queryphase_if_domain_small P f_0 T bound h_domain_size i_star h_small h_D_pos
  rw [div_le_iff₀ (Nat.cast_pos.mpr (h_D_pos 0))]
  grind
