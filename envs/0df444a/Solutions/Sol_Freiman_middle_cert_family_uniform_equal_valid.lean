-- Prove2me | solution 1 for Freiman.middle_cert_family_uniform_equal_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:25:38.064847+00:00
-- url     : https://prove2.me/submissions/f87bacc9-505e-444a-b5e1-60d583e8997a

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

namespace FastFamily9

private def selectedRecords : List MiddleCertRecord := [
  ⟨150,0,[-1],505⟩,
  ⟨150,1,[-1],522⟩,
  ⟨150,2,[-1],504⟩,
  ⟨150,3,[-1],504⟩,
  ⟨150,4,[-1],1203⟩,
  ⟨150,5,[-1],1231⟩,
  ⟨150,6,[-1],1202⟩,
  ⟨150,7,[-1],1202⟩,
  ⟨150,8,[-1],1035⟩,
  ⟨150,9,[-1],1040⟩,
  ⟨150,10,[-1],1034⟩,
  ⟨150,11,[-1],1034⟩,
  ⟨150,12,[-1],1203⟩,
  ⟨150,13,[-1],1231⟩,
  ⟨150,14,[-1],1202⟩,
  ⟨150,15,[-1],1202⟩,
  ⟨150,16,[-1],543⟩,
  ⟨150,17,[-1],561⟩,
  ⟨150,18,[-1],542⟩,
  ⟨150,19,[-1],542⟩,
  ⟨150,20,[-1],543⟩,
  ⟨150,21,[-1],561⟩,
  ⟨150,22,[-1],542⟩,
  ⟨150,23,[-1],542⟩,
  ⟨150,24,[-1],956⟩,
  ⟨150,25,[-1],974⟩,
  ⟨150,26,[-1],955⟩,
  ⟨150,27,[-1],955⟩,
  ⟨150,28,[-1],956⟩,
  ⟨150,29,[-1],974⟩,
  ⟨150,30,[-1],955⟩,
  ⟨150,31,[-1],955⟩,
  ⟨150,32,[-1],505⟩,
  ⟨150,33,[-1],522⟩,
  ⟨150,34,[-1],509⟩,
  ⟨150,35,[-1],524⟩,
  ⟨150,36,[-1],1203⟩,
  ⟨150,37,[-1],1231⟩,
  ⟨150,38,[-1],1211⟩,
  ⟨150,39,[-1],1235⟩,
  ⟨150,40,[-1],1035⟩,
  ⟨150,41,[-1],1040⟩,
  ⟨150,42,[-1],1036⟩,
  ⟨150,43,[-1],1039⟩,
  ⟨150,44,[-1],1203⟩,
  ⟨150,45,[-1],1231⟩,
  ⟨150,46,[-1],1211⟩,
  ⟨150,47,[-1],1223⟩,
  ⟨150,48,[-1],543⟩,
  ⟨150,49,[-1],561⟩,
  ⟨150,50,[-1],547⟩,
  ⟨150,51,[-1],557⟩,
  ⟨150,52,[-1],543⟩,
  ⟨150,53,[-1],561⟩,
  ⟨150,54,[-1],547⟩,
  ⟨150,55,[-1],557⟩,
  ⟨150,56,[-1],956⟩,
  ⟨150,57,[-1],974⟩,
  ⟨150,58,[-1],960⟩,
  ⟨150,59,[-1],971⟩,
  ⟨150,60,[-1],956⟩,
  ⟨150,61,[-1],974⟩,
  ⟨150,62,[-1],960⟩,
  ⟨150,63,[-1],971⟩
]

private def selectedGoals : List ℕ := [149]

private theorem records_eq :
    middleCertData.records.filter (fun r => decide ((middleCertGoal middleCertData r.goal).family = 9)) = selectedRecords := by
  decide +kernel

private theorem goals_eq :
    (List.range middleCertData.goals.length).filter (fun i => decide ((middleCertGoal middleCertData (i+1)).family = 9)) = selectedGoals := by
  decide +kernel

private theorem records_valid :
    ∀ r ∈ selectedRecords, middleCertRecordValid middleCertData r := by
  decide +kernel

private theorem coverage :
    ∀ i ∈ selectedGoals,
      ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData (i+1))).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData (i+1)) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (9 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 9)).length,
          ∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

end FastFamily9

open FastFamily9

theorem solution : middleCertFamilyValid middleCertData 9 := by
  have subset : ∀ r ∈ selectedRecords, r ∈ middleCertData.records := by
    intro r hr
    rw [← records_eq] at hr
    exact (List.mem_filter.mp hr).1
  have recorded (g b : ℕ) (p : ℤ) :
      (∃ r ∈ selectedRecords, r.goal = g ∧ r.branch = b ∧ p ∈ r.parents) →
      middleCertRecorded middleCertData g b p := by
    rintro ⟨r, hr, hg, hb, hp⟩
    exact ⟨r, subset r hr, hg, hb, hp⟩
  unfold middleCertFamilyValid
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · intro r hr hf
    apply records_valid r
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq] using hf⟩
  · intro i hi hf j hj
    have himem : i ∈ selectedGoals := by
      rw [← goals_eq]
      exact List.mem_filter.mpr ⟨hi, by simpa only [decide_eq_true_eq] using hf⟩
    rcases coverage i himem j hj with ha | hn | ⟨hf9, hp⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl (recorded _ _ _ hn))
    · exact Or.inr (Or.inr ⟨hf9, fun k hk => recorded _ _ _ (hp k hk)⟩)

#print axioms solution
