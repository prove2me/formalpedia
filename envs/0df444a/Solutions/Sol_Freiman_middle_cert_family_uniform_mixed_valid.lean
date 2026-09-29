-- Prove2me | solution 1 for Freiman.middle_cert_family_uniform_mixed_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T23:01:34.589225+00:00
-- url     : https://prove2.me/submissions/09830bc4-e66f-4538-ae5e-79431453ed46

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

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
    middleCertFamilyValid middleCertData 10 := by
  unfold middleCertFamilyValid
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · have hchunks : ∀ k ∈ List.range 259,
        ∀ rec ∈ (middleCertData.records.drop (16*k)).take 16,
          (middleCertGoal middleCertData rec.goal).family = 10 → middleCertRecordValid middleCertData rec := by
      intro k hk
      have hk' : k < 259 := List.mem_range.mp hk
      interval_cases k <;> decide +kernel
    have hcover : (List.range 259).flatMap (fun k => (middleCertData.records.drop (16*k)).take 16) =
        middleCertData.records := by decide +kernel
    intro rec hr
    rw [← hcover] at hr
    rcases List.mem_flatMap.mp hr with ⟨k, hk, hr⟩
    exact hchunks k hk rec hr
  · decide +kernel

#print axioms solution
