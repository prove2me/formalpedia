-- Prove2me | solution 1 for Freiman.middle_cert_family_mixed_A_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T23:00:48.604913+00:00
-- url     : https://prove2.me/submissions/51131cef-99ad-427b-b9f9-a22abd561ea4

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance (C : MiddleCertCatalog) (p : MiddleCertPair) (direction : ℤ) :
    Decidable (middleCertPairValid C p direction) := by
  unfold middleCertPairValid
  infer_instance
local instance (C : MiddleCertCatalog) (p : MiddleCertProof) :
    Decidable (middleCertProofValid C p) := by
  cases p <;> unfold middleCertProofValid <;> infer_instance
local instance (C : MiddleCertCatalog) (r : MiddleCertRecord) :
    Decidable (middleCertRecordValid C r) := by
  unfold middleCertRecordValid
  infer_instance
local instance (C : MiddleCertCatalog) (g : MiddleCertGoal) (sp : MiddleCertSpec) :
    Decidable (middleCertGoalMatches C g sp) := by
  unfold middleCertGoalMatches
  infer_instance
local instance (C : MiddleCertCatalog) (goal branch : ℕ) (parent : ℤ) :
    Decidable (middleCertRecorded C goal branch parent) := by
  unfold middleCertRecorded
  infer_instance

theorem solution :
    middleCertFamilyValid middleCertData 0 := by
  unfold middleCertFamilyValid
  refine ⟨?_, ?_, ?_⟩
  all_goals decide +kernel

#print axioms solution
