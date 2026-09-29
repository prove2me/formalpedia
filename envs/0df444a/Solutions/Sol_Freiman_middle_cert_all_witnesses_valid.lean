-- Prove2me | solution 1 for Freiman.middle_cert_all_witnesses_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:18.638827+00:00
-- url     : https://prove2.me/submissions/9a30859f-ba3e-497c-963e-51941ee08283

import Theorems.Thm_Freiman_middle_cert_witness_block_0
import Theorems.Thm_Freiman_middle_cert_witness_block_1
import Theorems.Thm_Freiman_middle_cert_witness_block_2
import Theorems.Thm_Freiman_middle_cert_witness_block_3
import Theorems.Thm_Freiman_middle_cert_witness_block_4
import Theorems.Thm_Freiman_middle_cert_witness_block_5
import Theorems.Thm_Freiman_middle_cert_witness_block_6
import Theorems.Thm_Freiman_middle_cert_witness_block_7
import Theorems.Thm_Freiman_middle_cert_witness_block_8
import Theorems.Thm_Freiman_middle_cert_witness_block_9
import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

theorem solution :
    middleCertWitnessesValid middleCertData := by
  intro w hw
  change w ∈ middleCertWitnesses0 ++ middleCertWitnesses1 ++ middleCertWitnesses2 ++ middleCertWitnesses3 ++ middleCertWitnesses4 ++ middleCertWitnesses5 ++ middleCertWitnesses6 ++ middleCertWitnesses7 ++ middleCertWitnesses8 ++ middleCertWitnesses9 at hw
  simp only [List.mem_append, or_assoc] at hw
  rcases hw with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact middle_cert_witness_block_0 w h0
  · exact middle_cert_witness_block_1 w h1
  · exact middle_cert_witness_block_2 w h2
  · exact middle_cert_witness_block_3 w h3
  · exact middle_cert_witness_block_4 w h4
  · exact middle_cert_witness_block_5 w h5
  · exact middle_cert_witness_block_6 w h6
  · exact middle_cert_witness_block_7 w h7
  · exact middle_cert_witness_block_8 w h8
  · exact middle_cert_witness_block_9 w h9
