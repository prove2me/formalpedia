-- Prove2me | solution 1 for FRI_claim_queryphase_if_domain_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:31:49.258703+00:00
-- url     : https://prove2.me/submissions/dd4dde51-8ce6-4a5b-a1f1-cccbd7746465

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_W_ratio_le

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (bound : ℝ)
    (h_domain_size : FRI_Domain_Size_Property P)
    (i_star : Fin (P.num_foldings + 1))
    (h_small : (FRI_W P f_0 T i_star).card <
      (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i_star).card)
    (h_D_pos : ∀ i : Fin (P.num_foldings + 1), (FRI_domain P i).card > 0) :
    (FRI_W P f_0 T 0).card < (1 - FRI_distance_star P f_0 bound) * (FRI_domain P 0).card := by
  have h_trans : ∀ i j : Fin (P.num_foldings + 1), i ≤ j →
      ((FRI_W P f_0 T i).card : ℝ) / (FRI_domain P i).card ≤
      ((FRI_W P f_0 T j).card : ℝ) / (FRI_domain P j).card := by
    intro i j hij
    induction j using Fin.induction generalizing i with
    | zero => simp_all
    | succ j ih =>
      cases hij.eq_or_lt with
      | inl h => simp_all
      | inr h =>
        exact (ih _ <| Nat.le_of_lt_succ h).trans
          (FRI_W_ratio_le P f_0 T h_domain_size _ <| Fin.castSucc_lt_last _)
  have := h_trans 0 i_star (Nat.zero_le _)
  rw [div_le_div_iff₀] at this
  · norm_num at *
    nlinarith [show ((FRI_domain P 0).card : ℝ) > 0
      from Nat.cast_pos.mpr (Finset.card_pos.mpr (h_D_pos 0))]
  · exact Nat.cast_pos.mpr (h_D_pos 0)
  · exact Nat.cast_pos.mpr (h_D_pos i_star)
