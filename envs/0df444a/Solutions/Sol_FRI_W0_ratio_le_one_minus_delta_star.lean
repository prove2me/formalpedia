-- Prove2me | solution 1 for FRI_W0_ratio_le_one_minus_delta_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:38:59.303211+00:00
-- url     : https://prove2.me/submissions/ab6698f6-e09b-4c28-b6b9-64d5881efbdc

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_State_false_implies_no_bad_event
import Theorems.Thm_FRI_W0_ratio_le_case_some_small
import Theorems.Thm_FRI_W0_ratio_le_case_all_large

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (bound : ℝ)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_pass : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings)
    (h_domain_size : FRI_Domain_Size_Property P)
    (h_D_pos : ∀ i : Fin (P.num_foldings + 1), (FRI_domain P i).card > 0) :
    ((FRI_W P f_0 T 0).card : ℝ) / (FRI_domain P 0).card ≤ 1 - FRI_distance_star P f_0 bound := by
  -- Case analysis on whether all W_i are large
  by_cases h_all_large : ∀ i : Fin (P.num_foldings + 1),
      (FRI_W P f_0 T i).card ≥ (1 - FRI_distance_star P f_0 bound) * (FRI_domain P i).card
  -- Case 1: All W_i are large
  · exact FRI_W0_ratio_le_case_all_large P f_0 T bound h_pass h_all_large
      (FRI_State_false_implies_no_bad_event P f_0 bound T h_state)
  -- Case 2: Some W_i is small
  · push_neg at h_all_large
    obtain ⟨i_star, h_small⟩ := h_all_large
    exact FRI_W0_ratio_le_case_some_small P f_0 T bound h_domain_size h_D_pos i_star h_small
