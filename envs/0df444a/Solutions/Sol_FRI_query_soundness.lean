-- Prove2me | solution 1 for FRI_query_soundness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:39.781805+00:00
-- url     : https://prove2.me/submissions/6e61f6cf-22fc-4ce8-9ee9-2a7ff24bc4f0

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_query_prob_zero_of_final_check_fail
import Theorems.Thm_FRI_W0_ratio_le_one_minus_delta_star
import Theorems.Thm_FRI_query_prob_le_W0_ratio_pow
import Theorems.Thm_FRI_D0_nonempty
import Theorems.Thm_FRI_domain_zero_eq_D0


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (h_state : ¬ FRI_State P f_0 bound T P.num_foldings)
    (h_domain_size : FRI_Domain_Size_Property P)
    (h_D_pos : ∀ i : Fin (P.num_foldings + 1), (FRI_domain P i).card > 0) :
    FRI_query_prob P f_0 bound T ≤
      ENNReal.ofReal ((1 - FRI_distance_star P f_0 bound) ^ P.q_rep) := by
  -- Case split on whether the final function is in the code
  by_cases h_pass : FRI_final_oracle P f_0 T ∈ FRI_code P P.num_foldings
  · -- Final check passes
    -- |W_0|/|D_0| ≤ 1 - δ*
    have h_ratio :=
      FRI_W0_ratio_le_one_minus_delta_star P f_0 T bound h_state h_pass h_domain_size h_D_pos
    rw [FRI_domain_zero_eq_D0 P] at h_ratio
    -- Combine: FRI_query_prob ≤ (|W_0|/|D_0|)^t ≤ (1 - δ*)^t
    calc FRI_query_prob P f_0 bound T
        ≤ ENNReal.ofReal ((((FRI_W P f_0 T 0).card : ℝ) / (P.D_0.card : ℝ)) ^ P.q_rep) :=
          FRI_query_prob_le_W0_ratio_pow P f_0 bound T h_state h_pass (FRI_D0_nonempty P).to_subtype
      _ ≤ ENNReal.ofReal ((1 - FRI_distance_star P f_0 bound) ^ P.q_rep) :=
          ENNReal.ofReal_le_ofReal (by gcongr)
  · -- Final check fails, probability is 0
    exact FRI_query_prob_zero_of_final_check_fail P f_0 T bound h_state h_pass ▸ zero_le
