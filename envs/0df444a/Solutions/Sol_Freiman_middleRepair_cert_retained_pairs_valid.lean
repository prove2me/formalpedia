-- Prove2me | solution 1 for Freiman.middleRepair_cert_retained_pairs_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:32:36.574416+00:00
-- url     : https://prove2.me/submissions/6ba40c4d-a0f7-4775-afd0-0340c259dd3c

import Theorems.Thm_Freiman_middleRepair_cert_retained_mixed_A_valid
import Theorems.Thm_Freiman_middleRepair_cert_retained_mixed_B_valid
import Theorems.Thm_Freiman_middleRepair_cert_retained_mixed_C_valid
import Theorems.Thm_Freiman_middleRepair_cert_retained_equal_I_short_valid
import Theorems.Thm_Freiman_middleRepair_cert_retained_equal_I_J_valid
import Theorems.Thm_Freiman_middleRepair_cert_retained_equal_II_a_valid
import Theorems.Thm_Freiman_middleRepair_cert_retained_equal_II_b_normal_valid
import Theorems.Thm_Freiman_middleRepair_cert_retained_equal_II_b_short_valid
import Theorems.Thm_Freiman_middleRepair_cert_retained_equal_II_b_J_valid
import Theorems.Thm_Freiman_middleRepair_cert_retained_uniform_valid

open Freiman

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Every record of the catalog names a goal whose family index is one of the eleven
rows of the middle-interval certificate table. -/
private theorem family_range :
    ∀ rec ∈ middleCertData.records,
      (middleCertGoal middleCertData rec.goal).family ∈
        ([0,1,2,3,4,5,6,7,8,9,10] : List ℕ) := by
  decide +kernel

theorem solution :
    ∀ rec ∈ middleCertData.records, ∀ parent ∈ rec.parents,
      middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) = none →
      middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hrec parent hparent hnone
  have hfam := family_range rec hrec
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfam
  rcases hfam with h | h | h | h | h | h | h | h | h | h | h
  · exact middleRepair_cert_retained_mixed_A_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_mixed_B_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_mixed_C_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_equal_I_short_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_equal_I_J_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_equal_II_a_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_equal_II_b_normal_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_equal_II_b_short_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_equal_II_b_J_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_uniform_valid rec hrec (by simp [h]) parent hparent hnone
  · exact middleRepair_cert_retained_uniform_valid rec hrec (by simp [h]) parent hparent hnone
