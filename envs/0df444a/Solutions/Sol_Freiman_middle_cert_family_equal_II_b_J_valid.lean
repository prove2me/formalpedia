-- Prove2me | solution 1 for Freiman.middle_cert_family_equal_II_b_J_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:09:51.096835+00:00
-- url     : https://prove2.me/submissions/f2a8244f-842e-4b8a-a7ee-b1319a318a57

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

set_option Elab.async false
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

namespace FastFamily8

private def selectedRecords : List MiddleCertRecord := [
  ⟨133,4,[-1],406⟩,
  ⟨133,6,[-1],734⟩,
  ⟨133,7,[-1],1135⟩,
  ⟨133,12,[-1],739⟩,
  ⟨133,13,[-1],739⟩,
  ⟨133,14,[-1],739⟩,
  ⟨134,1,[-1],407⟩,
  ⟨134,2,[-1],739⟩,
  ⟨134,3,[-1],739⟩,
  ⟨134,7,[-1],739⟩,
  ⟨134,8,[-1],745⟩,
  ⟨134,9,[-1],745⟩,
  ⟨134,11,[-1],1137⟩,
  ⟨134,13,[-1],1138⟩,
  ⟨134,17,[-1],407⟩,
  ⟨134,18,[-1],739⟩,
  ⟨134,19,[-1],739⟩,
  ⟨134,23,[-1],739⟩,
  ⟨134,24,[-1],744⟩,
  ⟨134,25,[-1],744⟩,
  ⟨134,27,[-1],1137⟩,
  ⟨134,29,[-1],1136⟩,
  ⟨136,0,[-1],424⟩,
  ⟨136,1,[-1],424⟩,
  ⟨136,2,[-1],424⟩,
  ⟨136,3,[-1],424⟩,
  ⟨136,4,[-1],424⟩,
  ⟨136,5,[-1],424⟩,
  ⟨136,6,[-1],424⟩,
  ⟨136,7,[-1],424⟩,
  ⟨136,8,[-1],450⟩,
  ⟨136,9,[-1],450⟩,
  ⟨136,10,[-1],450⟩,
  ⟨136,11,[-1],450⟩,
  ⟨136,12,[-1],450⟩,
  ⟨136,13,[-1],450⟩,
  ⟨136,14,[-1],450⟩,
  ⟨136,15,[-1],450⟩,
  ⟨136,16,[-1],423⟩,
  ⟨136,17,[-1],423⟩,
  ⟨136,18,[-1],423⟩,
  ⟨136,19,[-1],423⟩,
  ⟨136,20,[-1],426⟩,
  ⟨136,21,[-1],426⟩,
  ⟨136,22,[-1],426⟩,
  ⟨136,23,[-1],426⟩,
  ⟨136,24,[-1],423⟩,
  ⟨136,25,[-1],423⟩,
  ⟨136,26,[-1],423⟩,
  ⟨136,27,[-1],423⟩,
  ⟨136,28,[-1],443⟩,
  ⟨136,29,[-1],434⟩,
  ⟨136,30,[-1],438⟩,
  ⟨136,31,[-1],453⟩,
  ⟨136,32,[-1],424⟩,
  ⟨136,33,[-1],424⟩,
  ⟨136,34,[-1],424⟩,
  ⟨136,35,[-1],424⟩,
  ⟨136,36,[-1],424⟩,
  ⟨136,37,[-1],424⟩,
  ⟨136,38,[-1],424⟩,
  ⟨136,39,[-1],424⟩,
  ⟨136,40,[-1],450⟩,
  ⟨136,41,[-1],450⟩,
  ⟨136,42,[-1],450⟩,
  ⟨136,43,[-1],450⟩,
  ⟨136,44,[-1],450⟩,
  ⟨136,45,[-1],450⟩,
  ⟨136,46,[-1],450⟩,
  ⟨136,47,[-1],450⟩,
  ⟨136,48,[-1],423⟩,
  ⟨136,49,[-1],423⟩,
  ⟨136,50,[-1],423⟩,
  ⟨136,51,[-1],423⟩,
  ⟨136,52,[-1],426⟩,
  ⟨136,53,[-1],426⟩,
  ⟨136,54,[-1],426⟩,
  ⟨136,55,[-1],426⟩,
  ⟨136,56,[-1],423⟩,
  ⟨136,57,[-1],423⟩,
  ⟨136,58,[-1],423⟩,
  ⟨136,59,[-1],423⟩,
  ⟨136,60,[-1],443⟩,
  ⟨136,61,[-1],434⟩,
  ⟨136,62,[-1],438⟩,
  ⟨136,63,[-1],453⟩,
  ⟨137,0,[-1],224⟩,
  ⟨137,1,[-1],224⟩,
  ⟨137,2,[-1],224⟩,
  ⟨137,3,[-1],224⟩,
  ⟨137,4,[-1],799⟩,
  ⟨137,5,[-1],799⟩,
  ⟨137,6,[-1],799⟩,
  ⟨137,7,[-1],799⟩,
  ⟨137,8,[-1],929⟩,
  ⟨137,9,[-1],1121⟩,
  ⟨137,10,[-1],1193⟩,
  ⟨137,11,[-1],669⟩,
  ⟨137,12,[-1],799⟩,
  ⟨137,13,[-1],799⟩,
  ⟨137,14,[-1],799⟩,
  ⟨137,15,[-1],799⟩,
  ⟨137,16,[-1],1175⟩,
  ⟨137,17,[-1],1175⟩,
  ⟨137,18,[-1],1175⟩,
  ⟨137,19,[-1],1175⟩,
  ⟨137,20,[-1],1175⟩,
  ⟨137,21,[-1],1175⟩,
  ⟨137,22,[-1],1175⟩,
  ⟨137,23,[-1],1175⟩,
  ⟨137,24,[-1],997⟩,
  ⟨137,25,[-1],997⟩,
  ⟨137,26,[-1],997⟩,
  ⟨137,27,[-1],997⟩,
  ⟨137,28,[-1],997⟩,
  ⟨137,29,[-1],997⟩,
  ⟨137,30,[-1],997⟩,
  ⟨137,31,[-1],997⟩,
  ⟨137,32,[-1],224⟩,
  ⟨137,33,[-1],224⟩,
  ⟨137,34,[-1],224⟩,
  ⟨137,35,[-1],224⟩,
  ⟨137,36,[-1],799⟩,
  ⟨137,37,[-1],799⟩,
  ⟨137,38,[-1],799⟩,
  ⟨137,39,[-1],799⟩,
  ⟨137,40,[-1],929⟩,
  ⟨137,41,[-1],1121⟩,
  ⟨137,42,[-1],1193⟩,
  ⟨137,43,[-1],669⟩,
  ⟨137,44,[-1],799⟩,
  ⟨137,45,[-1],799⟩,
  ⟨137,46,[-1],799⟩,
  ⟨137,47,[-1],799⟩,
  ⟨137,48,[-1],1175⟩,
  ⟨137,49,[-1],1175⟩,
  ⟨137,50,[-1],1175⟩,
  ⟨137,51,[-1],1175⟩,
  ⟨137,52,[-1],1175⟩,
  ⟨137,53,[-1],1175⟩,
  ⟨137,54,[-1],1175⟩,
  ⟨137,55,[-1],1175⟩,
  ⟨137,56,[-1],997⟩,
  ⟨137,57,[-1],997⟩,
  ⟨137,58,[-1],997⟩,
  ⟨137,59,[-1],997⟩,
  ⟨137,60,[-1],997⟩,
  ⟨137,61,[-1],997⟩,
  ⟨137,62,[-1],997⟩,
  ⟨137,63,[-1],997⟩,
  ⟨139,0,[-1],419⟩,
  ⟨139,1,[-1],451⟩,
  ⟨139,2,[-1],427⟩,
  ⟨139,3,[-1],454⟩,
  ⟨139,4,[-1],419⟩,
  ⟨139,5,[-1],451⟩,
  ⟨139,6,[-1],436⟩,
  ⟨139,7,[-1],433⟩,
  ⟨139,8,[-1],419⟩,
  ⟨139,9,[-1],451⟩,
  ⟨139,10,[-1],427⟩,
  ⟨139,11,[-1],432⟩,
  ⟨139,12,[-1],419⟩,
  ⟨139,13,[-1],451⟩,
  ⟨139,14,[-1],427⟩,
  ⟨139,15,[-1],447⟩,
  ⟨140,0,[-1],414⟩,
  ⟨140,1,[-1],441⟩,
  ⟨140,2,[-1],468⟩,
  ⟨140,3,[-1],468⟩,
  ⟨140,4,[-1],414⟩,
  ⟨140,5,[-1],441⟩,
  ⟨140,6,[-1],905⟩,
  ⟨140,7,[-1],614⟩,
  ⟨140,8,[-1],716⟩,
  ⟨140,9,[-1],720⟩,
  ⟨140,10,[-1],719⟩,
  ⟨140,11,[-1],719⟩,
  ⟨140,12,[-1],1163⟩,
  ⟨140,13,[-1],1165⟩,
  ⟨140,14,[-1],1164⟩,
  ⟨140,15,[-1],1164⟩,
  ⟨142,0,[-1],416⟩,
  ⟨142,1,[-1],455⟩,
  ⟨142,2,[-1],420⟩,
  ⟨142,3,[-1],456⟩,
  ⟨142,4,[-1],416⟩,
  ⟨142,5,[-1],455⟩,
  ⟨142,6,[-1],429⟩,
  ⟨142,7,[-1],439⟩,
  ⟨142,8,[-1],416⟩,
  ⟨142,9,[-1],455⟩,
  ⟨142,10,[-1],420⟩,
  ⟨142,11,[-1],428⟩,
  ⟨142,12,[-1],416⟩,
  ⟨142,13,[-1],455⟩,
  ⟨142,14,[-1],420⟩,
  ⟨142,15,[-1],448⟩,
  ⟨143,0,[-1],8⟩,
  ⟨143,1,[-1],8⟩,
  ⟨143,2,[-1],8⟩,
  ⟨143,3,[-1],8⟩,
  ⟨143,4,[-1],592⟩,
  ⟨143,5,[-1],705⟩,
  ⟨143,6,[-1],599⟩,
  ⟨143,7,[-1],1002⟩,
  ⟨143,8,[-1],763⟩,
  ⟨143,9,[-1],763⟩,
  ⟨143,10,[-1],763⟩,
  ⟨143,11,[-1],763⟩,
  ⟨143,12,[-1],687⟩,
  ⟨143,13,[-1],687⟩,
  ⟨143,14,[-1],687⟩,
  ⟨143,15,[-1],687⟩,
  ⟨144,0,[-1],415⟩,
  ⟨144,1,[-1],444⟩,
  ⟨144,2,[-1],425⟩,
  ⟨144,3,[-1],417⟩,
  ⟨144,4,[-1],415⟩,
  ⟨144,5,[-1],444⟩,
  ⟨144,6,[-1],425⟩,
  ⟨144,7,[-1],446⟩,
  ⟨144,8,[-1],415⟩,
  ⟨144,9,[-1],444⟩,
  ⟨144,10,[-1],425⟩,
  ⟨144,11,[-1],417⟩,
  ⟨144,12,[-1],415⟩,
  ⟨144,13,[-1],444⟩,
  ⟨144,14,[-1],425⟩,
  ⟨144,15,[-1],431⟩,
  ⟨144,16,[-1],415⟩,
  ⟨144,17,[-1],444⟩,
  ⟨144,18,[-1],425⟩,
  ⟨144,19,[-1],417⟩,
  ⟨144,20,[-1],415⟩,
  ⟨144,21,[-1],444⟩,
  ⟨144,22,[-1],425⟩,
  ⟨144,23,[-1],435⟩,
  ⟨144,24,[-1],1106⟩,
  ⟨144,25,[-1],1111⟩,
  ⟨144,26,[-1],1109⟩,
  ⟨144,27,[-1],1107⟩,
  ⟨144,28,[-1],1106⟩,
  ⟨144,29,[-1],1111⟩,
  ⟨144,30,[-1],1109⟩,
  ⟨144,31,[-1],1113⟩,
  ⟨146,0,[-1],418⟩,
  ⟨146,1,[-1],445⟩,
  ⟨146,2,[-1],417⟩,
  ⟨146,3,[-1],417⟩,
  ⟨146,4,[-1],418⟩,
  ⟨146,5,[-1],445⟩,
  ⟨146,6,[-1],417⟩,
  ⟨146,7,[-1],417⟩,
  ⟨146,8,[-1],418⟩,
  ⟨146,9,[-1],445⟩,
  ⟨146,10,[-1],417⟩,
  ⟨146,11,[-1],417⟩,
  ⟨146,12,[-1],418⟩,
  ⟨146,13,[-1],445⟩,
  ⟨146,14,[-1],417⟩,
  ⟨146,15,[-1],417⟩,
  ⟨146,16,[-1],418⟩,
  ⟨146,17,[-1],445⟩,
  ⟨146,18,[-1],417⟩,
  ⟨146,19,[-1],417⟩,
  ⟨146,20,[-1],418⟩,
  ⟨146,21,[-1],445⟩,
  ⟨146,22,[-1],417⟩,
  ⟨146,23,[-1],417⟩,
  ⟨146,24,[-1],418⟩,
  ⟨146,25,[-1],445⟩,
  ⟨146,26,[-1],417⟩,
  ⟨146,27,[-1],417⟩,
  ⟨146,28,[-1],418⟩,
  ⟨146,29,[-1],445⟩,
  ⟨146,30,[-1],417⟩,
  ⟨146,31,[-1],417⟩,
  ⟨146,32,[-1],418⟩,
  ⟨146,33,[-1],445⟩,
  ⟨146,34,[-1],422⟩,
  ⟨146,35,[-1],452⟩,
  ⟨146,36,[-1],418⟩,
  ⟨146,37,[-1],445⟩,
  ⟨146,38,[-1],422⟩,
  ⟨146,39,[-1],452⟩,
  ⟨146,40,[-1],418⟩,
  ⟨146,41,[-1],445⟩,
  ⟨146,42,[-1],422⟩,
  ⟨146,43,[-1],437⟩,
  ⟨146,44,[-1],418⟩,
  ⟨146,45,[-1],445⟩,
  ⟨146,46,[-1],422⟩,
  ⟨146,47,[-1],437⟩,
  ⟨146,48,[-1],418⟩,
  ⟨146,49,[-1],445⟩,
  ⟨146,50,[-1],422⟩,
  ⟨146,51,[-1],440⟩,
  ⟨146,52,[-1],418⟩,
  ⟨146,53,[-1],445⟩,
  ⟨146,54,[-1],422⟩,
  ⟨146,55,[-1],440⟩,
  ⟨146,56,[-1],418⟩,
  ⟨146,57,[-1],445⟩,
  ⟨146,58,[-1],422⟩,
  ⟨146,59,[-1],442⟩,
  ⟨146,60,[-1],418⟩,
  ⟨146,61,[-1],445⟩,
  ⟨146,62,[-1],422⟩,
  ⟨146,63,[-1],442⟩,
  ⟨148,0,[-1],1123⟩,
  ⟨148,1,[-1],1177⟩,
  ⟨148,2,[-1],1012⟩,
  ⟨148,3,[-1],899⟩,
  ⟨148,4,[-1],664⟩,
  ⟨148,5,[-1],1018⟩,
  ⟨148,6,[-1],1115⟩,
  ⟨148,7,[-1],1118⟩,
  ⟨148,8,[-1],754⟩,
  ⟨148,9,[-1],758⟩,
  ⟨148,10,[-1],755⟩,
  ⟨148,11,[-1],755⟩,
  ⟨148,12,[-1],1146⟩,
  ⟨148,13,[-1],1148⟩,
  ⟨148,14,[-1],1146⟩,
  ⟨148,15,[-1],1146⟩,
  ⟨149,8,[-1],457⟩,
  ⟨149,9,[-1],430⟩,
  ⟨149,10,[-1],756⟩,
  ⟨149,11,[-1],1153⟩
]

private def selectedGoals : List ℕ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]

private theorem records_eq :
    middleCertData.records.filter (fun r => decide ((middleCertGoal middleCertData r.goal).family = 8)) = selectedRecords := by
  decide +kernel

private theorem goals_eq :
    (List.range middleCertData.goals.length).filter (fun i => decide ((middleCertGoal middleCertData (i+1)).family = 8)) = selectedGoals := by
  decide +kernel

private def chunk_0 : List MiddleCertRecord := [
  ⟨133,4,[-1],406⟩,
  ⟨133,6,[-1],734⟩,
  ⟨133,7,[-1],1135⟩,
  ⟨133,12,[-1],739⟩,
  ⟨133,13,[-1],739⟩,
  ⟨133,14,[-1],739⟩,
  ⟨134,1,[-1],407⟩,
  ⟨134,2,[-1],739⟩,
  ⟨134,3,[-1],739⟩,
  ⟨134,7,[-1],739⟩,
  ⟨134,8,[-1],745⟩,
  ⟨134,9,[-1],745⟩,
  ⟨134,11,[-1],1137⟩,
  ⟨134,13,[-1],1138⟩,
  ⟨134,17,[-1],407⟩,
  ⟨134,18,[-1],739⟩
]

private theorem chunk_valid_0 : ∀ r ∈ chunk_0, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨134,19,[-1],739⟩,
  ⟨134,23,[-1],739⟩,
  ⟨134,24,[-1],744⟩,
  ⟨134,25,[-1],744⟩,
  ⟨134,27,[-1],1137⟩,
  ⟨134,29,[-1],1136⟩,
  ⟨136,0,[-1],424⟩,
  ⟨136,1,[-1],424⟩,
  ⟨136,2,[-1],424⟩,
  ⟨136,3,[-1],424⟩,
  ⟨136,4,[-1],424⟩,
  ⟨136,5,[-1],424⟩,
  ⟨136,6,[-1],424⟩,
  ⟨136,7,[-1],424⟩,
  ⟨136,8,[-1],450⟩,
  ⟨136,9,[-1],450⟩
]

private theorem chunk_valid_1 : ∀ r ∈ chunk_1, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨136,10,[-1],450⟩,
  ⟨136,11,[-1],450⟩,
  ⟨136,12,[-1],450⟩,
  ⟨136,13,[-1],450⟩,
  ⟨136,14,[-1],450⟩,
  ⟨136,15,[-1],450⟩,
  ⟨136,16,[-1],423⟩,
  ⟨136,17,[-1],423⟩,
  ⟨136,18,[-1],423⟩,
  ⟨136,19,[-1],423⟩,
  ⟨136,20,[-1],426⟩,
  ⟨136,21,[-1],426⟩,
  ⟨136,22,[-1],426⟩,
  ⟨136,23,[-1],426⟩,
  ⟨136,24,[-1],423⟩,
  ⟨136,25,[-1],423⟩
]

private theorem chunk_valid_2 : ∀ r ∈ chunk_2, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨136,26,[-1],423⟩,
  ⟨136,27,[-1],423⟩,
  ⟨136,28,[-1],443⟩,
  ⟨136,29,[-1],434⟩,
  ⟨136,30,[-1],438⟩,
  ⟨136,31,[-1],453⟩,
  ⟨136,32,[-1],424⟩,
  ⟨136,33,[-1],424⟩,
  ⟨136,34,[-1],424⟩,
  ⟨136,35,[-1],424⟩,
  ⟨136,36,[-1],424⟩,
  ⟨136,37,[-1],424⟩,
  ⟨136,38,[-1],424⟩,
  ⟨136,39,[-1],424⟩,
  ⟨136,40,[-1],450⟩,
  ⟨136,41,[-1],450⟩
]

private theorem chunk_valid_3 : ∀ r ∈ chunk_3, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨136,42,[-1],450⟩,
  ⟨136,43,[-1],450⟩,
  ⟨136,44,[-1],450⟩,
  ⟨136,45,[-1],450⟩,
  ⟨136,46,[-1],450⟩,
  ⟨136,47,[-1],450⟩,
  ⟨136,48,[-1],423⟩,
  ⟨136,49,[-1],423⟩,
  ⟨136,50,[-1],423⟩,
  ⟨136,51,[-1],423⟩,
  ⟨136,52,[-1],426⟩,
  ⟨136,53,[-1],426⟩,
  ⟨136,54,[-1],426⟩,
  ⟨136,55,[-1],426⟩,
  ⟨136,56,[-1],423⟩,
  ⟨136,57,[-1],423⟩
]

private theorem chunk_valid_4 : ∀ r ∈ chunk_4, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨136,58,[-1],423⟩,
  ⟨136,59,[-1],423⟩,
  ⟨136,60,[-1],443⟩,
  ⟨136,61,[-1],434⟩,
  ⟨136,62,[-1],438⟩,
  ⟨136,63,[-1],453⟩,
  ⟨137,0,[-1],224⟩,
  ⟨137,1,[-1],224⟩,
  ⟨137,2,[-1],224⟩,
  ⟨137,3,[-1],224⟩,
  ⟨137,4,[-1],799⟩,
  ⟨137,5,[-1],799⟩,
  ⟨137,6,[-1],799⟩,
  ⟨137,7,[-1],799⟩,
  ⟨137,8,[-1],929⟩,
  ⟨137,9,[-1],1121⟩
]

private theorem chunk_valid_5 : ∀ r ∈ chunk_5, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨137,10,[-1],1193⟩,
  ⟨137,11,[-1],669⟩,
  ⟨137,12,[-1],799⟩,
  ⟨137,13,[-1],799⟩,
  ⟨137,14,[-1],799⟩,
  ⟨137,15,[-1],799⟩,
  ⟨137,16,[-1],1175⟩,
  ⟨137,17,[-1],1175⟩,
  ⟨137,18,[-1],1175⟩,
  ⟨137,19,[-1],1175⟩,
  ⟨137,20,[-1],1175⟩,
  ⟨137,21,[-1],1175⟩,
  ⟨137,22,[-1],1175⟩,
  ⟨137,23,[-1],1175⟩,
  ⟨137,24,[-1],997⟩,
  ⟨137,25,[-1],997⟩
]

private theorem chunk_valid_6 : ∀ r ∈ chunk_6, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨137,26,[-1],997⟩,
  ⟨137,27,[-1],997⟩,
  ⟨137,28,[-1],997⟩,
  ⟨137,29,[-1],997⟩,
  ⟨137,30,[-1],997⟩,
  ⟨137,31,[-1],997⟩,
  ⟨137,32,[-1],224⟩,
  ⟨137,33,[-1],224⟩,
  ⟨137,34,[-1],224⟩,
  ⟨137,35,[-1],224⟩,
  ⟨137,36,[-1],799⟩,
  ⟨137,37,[-1],799⟩,
  ⟨137,38,[-1],799⟩,
  ⟨137,39,[-1],799⟩,
  ⟨137,40,[-1],929⟩,
  ⟨137,41,[-1],1121⟩
]

private theorem chunk_valid_7 : ∀ r ∈ chunk_7, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨137,42,[-1],1193⟩,
  ⟨137,43,[-1],669⟩,
  ⟨137,44,[-1],799⟩,
  ⟨137,45,[-1],799⟩,
  ⟨137,46,[-1],799⟩,
  ⟨137,47,[-1],799⟩,
  ⟨137,48,[-1],1175⟩,
  ⟨137,49,[-1],1175⟩,
  ⟨137,50,[-1],1175⟩,
  ⟨137,51,[-1],1175⟩,
  ⟨137,52,[-1],1175⟩,
  ⟨137,53,[-1],1175⟩,
  ⟨137,54,[-1],1175⟩,
  ⟨137,55,[-1],1175⟩,
  ⟨137,56,[-1],997⟩,
  ⟨137,57,[-1],997⟩
]

private theorem chunk_valid_8 : ∀ r ∈ chunk_8, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨137,58,[-1],997⟩,
  ⟨137,59,[-1],997⟩,
  ⟨137,60,[-1],997⟩,
  ⟨137,61,[-1],997⟩,
  ⟨137,62,[-1],997⟩,
  ⟨137,63,[-1],997⟩,
  ⟨139,0,[-1],419⟩,
  ⟨139,1,[-1],451⟩,
  ⟨139,2,[-1],427⟩,
  ⟨139,3,[-1],454⟩,
  ⟨139,4,[-1],419⟩,
  ⟨139,5,[-1],451⟩,
  ⟨139,6,[-1],436⟩,
  ⟨139,7,[-1],433⟩,
  ⟨139,8,[-1],419⟩,
  ⟨139,9,[-1],451⟩
]

private theorem chunk_valid_9 : ∀ r ∈ chunk_9, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨139,10,[-1],427⟩,
  ⟨139,11,[-1],432⟩,
  ⟨139,12,[-1],419⟩,
  ⟨139,13,[-1],451⟩,
  ⟨139,14,[-1],427⟩,
  ⟨139,15,[-1],447⟩,
  ⟨140,0,[-1],414⟩,
  ⟨140,1,[-1],441⟩,
  ⟨140,2,[-1],468⟩,
  ⟨140,3,[-1],468⟩,
  ⟨140,4,[-1],414⟩,
  ⟨140,5,[-1],441⟩,
  ⟨140,6,[-1],905⟩,
  ⟨140,7,[-1],614⟩,
  ⟨140,8,[-1],716⟩,
  ⟨140,9,[-1],720⟩
]

private theorem chunk_valid_10 : ∀ r ∈ chunk_10, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨140,10,[-1],719⟩,
  ⟨140,11,[-1],719⟩,
  ⟨140,12,[-1],1163⟩,
  ⟨140,13,[-1],1165⟩,
  ⟨140,14,[-1],1164⟩,
  ⟨140,15,[-1],1164⟩,
  ⟨142,0,[-1],416⟩,
  ⟨142,1,[-1],455⟩,
  ⟨142,2,[-1],420⟩,
  ⟨142,3,[-1],456⟩,
  ⟨142,4,[-1],416⟩,
  ⟨142,5,[-1],455⟩,
  ⟨142,6,[-1],429⟩,
  ⟨142,7,[-1],439⟩,
  ⟨142,8,[-1],416⟩,
  ⟨142,9,[-1],455⟩
]

private theorem chunk_valid_11 : ∀ r ∈ chunk_11, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨142,10,[-1],420⟩,
  ⟨142,11,[-1],428⟩,
  ⟨142,12,[-1],416⟩,
  ⟨142,13,[-1],455⟩,
  ⟨142,14,[-1],420⟩,
  ⟨142,15,[-1],448⟩,
  ⟨143,0,[-1],8⟩,
  ⟨143,1,[-1],8⟩,
  ⟨143,2,[-1],8⟩,
  ⟨143,3,[-1],8⟩,
  ⟨143,4,[-1],592⟩,
  ⟨143,5,[-1],705⟩,
  ⟨143,6,[-1],599⟩,
  ⟨143,7,[-1],1002⟩,
  ⟨143,8,[-1],763⟩,
  ⟨143,9,[-1],763⟩
]

private theorem chunk_valid_12 : ∀ r ∈ chunk_12, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨143,10,[-1],763⟩,
  ⟨143,11,[-1],763⟩,
  ⟨143,12,[-1],687⟩,
  ⟨143,13,[-1],687⟩,
  ⟨143,14,[-1],687⟩,
  ⟨143,15,[-1],687⟩,
  ⟨144,0,[-1],415⟩,
  ⟨144,1,[-1],444⟩,
  ⟨144,2,[-1],425⟩,
  ⟨144,3,[-1],417⟩,
  ⟨144,4,[-1],415⟩,
  ⟨144,5,[-1],444⟩,
  ⟨144,6,[-1],425⟩,
  ⟨144,7,[-1],446⟩,
  ⟨144,8,[-1],415⟩,
  ⟨144,9,[-1],444⟩
]

private theorem chunk_valid_13 : ∀ r ∈ chunk_13, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨144,10,[-1],425⟩,
  ⟨144,11,[-1],417⟩,
  ⟨144,12,[-1],415⟩,
  ⟨144,13,[-1],444⟩,
  ⟨144,14,[-1],425⟩,
  ⟨144,15,[-1],431⟩,
  ⟨144,16,[-1],415⟩,
  ⟨144,17,[-1],444⟩,
  ⟨144,18,[-1],425⟩,
  ⟨144,19,[-1],417⟩,
  ⟨144,20,[-1],415⟩,
  ⟨144,21,[-1],444⟩,
  ⟨144,22,[-1],425⟩,
  ⟨144,23,[-1],435⟩,
  ⟨144,24,[-1],1106⟩,
  ⟨144,25,[-1],1111⟩
]

private theorem chunk_valid_14 : ∀ r ∈ chunk_14, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨144,26,[-1],1109⟩,
  ⟨144,27,[-1],1107⟩,
  ⟨144,28,[-1],1106⟩,
  ⟨144,29,[-1],1111⟩,
  ⟨144,30,[-1],1109⟩,
  ⟨144,31,[-1],1113⟩,
  ⟨146,0,[-1],418⟩,
  ⟨146,1,[-1],445⟩,
  ⟨146,2,[-1],417⟩,
  ⟨146,3,[-1],417⟩,
  ⟨146,4,[-1],418⟩,
  ⟨146,5,[-1],445⟩,
  ⟨146,6,[-1],417⟩,
  ⟨146,7,[-1],417⟩,
  ⟨146,8,[-1],418⟩,
  ⟨146,9,[-1],445⟩
]

private theorem chunk_valid_15 : ∀ r ∈ chunk_15, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨146,10,[-1],417⟩,
  ⟨146,11,[-1],417⟩,
  ⟨146,12,[-1],418⟩,
  ⟨146,13,[-1],445⟩,
  ⟨146,14,[-1],417⟩,
  ⟨146,15,[-1],417⟩,
  ⟨146,16,[-1],418⟩,
  ⟨146,17,[-1],445⟩,
  ⟨146,18,[-1],417⟩,
  ⟨146,19,[-1],417⟩,
  ⟨146,20,[-1],418⟩,
  ⟨146,21,[-1],445⟩,
  ⟨146,22,[-1],417⟩,
  ⟨146,23,[-1],417⟩,
  ⟨146,24,[-1],418⟩,
  ⟨146,25,[-1],445⟩
]

private theorem chunk_valid_16 : ∀ r ∈ chunk_16, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨146,26,[-1],417⟩,
  ⟨146,27,[-1],417⟩,
  ⟨146,28,[-1],418⟩,
  ⟨146,29,[-1],445⟩,
  ⟨146,30,[-1],417⟩,
  ⟨146,31,[-1],417⟩,
  ⟨146,32,[-1],418⟩,
  ⟨146,33,[-1],445⟩,
  ⟨146,34,[-1],422⟩,
  ⟨146,35,[-1],452⟩,
  ⟨146,36,[-1],418⟩,
  ⟨146,37,[-1],445⟩,
  ⟨146,38,[-1],422⟩,
  ⟨146,39,[-1],452⟩,
  ⟨146,40,[-1],418⟩,
  ⟨146,41,[-1],445⟩
]

private theorem chunk_valid_17 : ∀ r ∈ chunk_17, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_18 : List MiddleCertRecord := [
  ⟨146,42,[-1],422⟩,
  ⟨146,43,[-1],437⟩,
  ⟨146,44,[-1],418⟩,
  ⟨146,45,[-1],445⟩,
  ⟨146,46,[-1],422⟩,
  ⟨146,47,[-1],437⟩,
  ⟨146,48,[-1],418⟩,
  ⟨146,49,[-1],445⟩,
  ⟨146,50,[-1],422⟩,
  ⟨146,51,[-1],440⟩,
  ⟨146,52,[-1],418⟩,
  ⟨146,53,[-1],445⟩,
  ⟨146,54,[-1],422⟩,
  ⟨146,55,[-1],440⟩,
  ⟨146,56,[-1],418⟩,
  ⟨146,57,[-1],445⟩
]

private theorem chunk_valid_18 : ∀ r ∈ chunk_18, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_19 : List MiddleCertRecord := [
  ⟨146,58,[-1],422⟩,
  ⟨146,59,[-1],442⟩,
  ⟨146,60,[-1],418⟩,
  ⟨146,61,[-1],445⟩,
  ⟨146,62,[-1],422⟩,
  ⟨146,63,[-1],442⟩,
  ⟨148,0,[-1],1123⟩,
  ⟨148,1,[-1],1177⟩,
  ⟨148,2,[-1],1012⟩,
  ⟨148,3,[-1],899⟩,
  ⟨148,4,[-1],664⟩,
  ⟨148,5,[-1],1018⟩,
  ⟨148,6,[-1],1115⟩,
  ⟨148,7,[-1],1118⟩,
  ⟨148,8,[-1],754⟩,
  ⟨148,9,[-1],758⟩
]

private theorem chunk_valid_19 : ∀ r ∈ chunk_19, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_20 : List MiddleCertRecord := [
  ⟨148,10,[-1],755⟩,
  ⟨148,11,[-1],755⟩,
  ⟨148,12,[-1],1146⟩,
  ⟨148,13,[-1],1148⟩,
  ⟨148,14,[-1],1146⟩,
  ⟨148,15,[-1],1146⟩,
  ⟨149,8,[-1],457⟩,
  ⟨149,9,[-1],430⟩,
  ⟨149,10,[-1],756⟩,
  ⟨149,11,[-1],1153⟩
]

private theorem chunk_valid_20 : ∀ r ∈ chunk_20, middleCertRecordValid middleCertData r := by
  decide +kernel

private theorem chunks_eq : [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20].flatten = selectedRecords := by
  decide +kernel

private theorem chunks_valid : ∀ rs ∈ [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20], ∀ r ∈ rs, middleCertRecordValid middleCertData r := by
  simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨chunk_valid_0, chunk_valid_1, chunk_valid_2, chunk_valid_3, chunk_valid_4, chunk_valid_5, chunk_valid_6, chunk_valid_7, chunk_valid_8, chunk_valid_9, chunk_valid_10, chunk_valid_11, chunk_valid_12, chunk_valid_13, chunk_valid_14, chunk_valid_15, chunk_valid_16, chunk_valid_17, chunk_valid_18, chunk_valid_19, chunk_valid_20, List.forall_mem_nil _⟩

private theorem records_valid :
    ∀ r ∈ selectedRecords, middleCertRecordValid middleCertData r := by
  intro r hr
  rw [← chunks_eq] at hr
  rcases List.mem_flatten.mp hr with ⟨rs, hrs, hr⟩
  exact chunks_valid rs hrs r hr

private def goalRecords_132 : List MiddleCertRecord := [
  ⟨133,4,[-1],406⟩,
  ⟨133,6,[-1],734⟩,
  ⟨133,7,[-1],1135⟩,
  ⟨133,12,[-1],739⟩,
  ⟨133,13,[-1],739⟩,
  ⟨133,14,[-1],739⟩
]

private theorem goal_subset_132 : ∀ r ∈ goalRecords_132, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_132 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 133)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 133) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_132, r.goal = 133 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_132, r.goal = 133 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_132 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 133)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 133) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 133 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 133 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_132 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_132 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_132 r hr, hg, hb, hp⟩

private def goalRecords_133 : List MiddleCertRecord := [
  ⟨134,1,[-1],407⟩,
  ⟨134,2,[-1],739⟩,
  ⟨134,3,[-1],739⟩,
  ⟨134,7,[-1],739⟩,
  ⟨134,8,[-1],745⟩,
  ⟨134,9,[-1],745⟩,
  ⟨134,11,[-1],1137⟩,
  ⟨134,13,[-1],1138⟩,
  ⟨134,17,[-1],407⟩,
  ⟨134,18,[-1],739⟩,
  ⟨134,19,[-1],739⟩,
  ⟨134,23,[-1],739⟩,
  ⟨134,24,[-1],744⟩,
  ⟨134,25,[-1],744⟩,
  ⟨134,27,[-1],1137⟩,
  ⟨134,29,[-1],1136⟩
]

private theorem goal_subset_133 : ∀ r ∈ goalRecords_133, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_133 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 134)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 134) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_133, r.goal = 134 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_133, r.goal = 134 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_133 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 134)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 134) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 134 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 134 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_133 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_133 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_133 r hr, hg, hb, hp⟩

private def goalRecords_134 : List MiddleCertRecord := [

]

private theorem goal_subset_134 : ∀ r ∈ goalRecords_134, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_134 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 135)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 135) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_134, r.goal = 135 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_134, r.goal = 135 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_134 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 135)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 135) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 135 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 135 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_134 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_134 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_134 r hr, hg, hb, hp⟩

private def goalRecords_135 : List MiddleCertRecord := [
  ⟨136,0,[-1],424⟩,
  ⟨136,1,[-1],424⟩,
  ⟨136,2,[-1],424⟩,
  ⟨136,3,[-1],424⟩,
  ⟨136,4,[-1],424⟩,
  ⟨136,5,[-1],424⟩,
  ⟨136,6,[-1],424⟩,
  ⟨136,7,[-1],424⟩,
  ⟨136,8,[-1],450⟩,
  ⟨136,9,[-1],450⟩,
  ⟨136,10,[-1],450⟩,
  ⟨136,11,[-1],450⟩,
  ⟨136,12,[-1],450⟩,
  ⟨136,13,[-1],450⟩,
  ⟨136,14,[-1],450⟩,
  ⟨136,15,[-1],450⟩,
  ⟨136,16,[-1],423⟩,
  ⟨136,17,[-1],423⟩,
  ⟨136,18,[-1],423⟩,
  ⟨136,19,[-1],423⟩,
  ⟨136,20,[-1],426⟩,
  ⟨136,21,[-1],426⟩,
  ⟨136,22,[-1],426⟩,
  ⟨136,23,[-1],426⟩,
  ⟨136,24,[-1],423⟩,
  ⟨136,25,[-1],423⟩,
  ⟨136,26,[-1],423⟩,
  ⟨136,27,[-1],423⟩,
  ⟨136,28,[-1],443⟩,
  ⟨136,29,[-1],434⟩,
  ⟨136,30,[-1],438⟩,
  ⟨136,31,[-1],453⟩,
  ⟨136,32,[-1],424⟩,
  ⟨136,33,[-1],424⟩,
  ⟨136,34,[-1],424⟩,
  ⟨136,35,[-1],424⟩,
  ⟨136,36,[-1],424⟩,
  ⟨136,37,[-1],424⟩,
  ⟨136,38,[-1],424⟩,
  ⟨136,39,[-1],424⟩,
  ⟨136,40,[-1],450⟩,
  ⟨136,41,[-1],450⟩,
  ⟨136,42,[-1],450⟩,
  ⟨136,43,[-1],450⟩,
  ⟨136,44,[-1],450⟩,
  ⟨136,45,[-1],450⟩,
  ⟨136,46,[-1],450⟩,
  ⟨136,47,[-1],450⟩,
  ⟨136,48,[-1],423⟩,
  ⟨136,49,[-1],423⟩,
  ⟨136,50,[-1],423⟩,
  ⟨136,51,[-1],423⟩,
  ⟨136,52,[-1],426⟩,
  ⟨136,53,[-1],426⟩,
  ⟨136,54,[-1],426⟩,
  ⟨136,55,[-1],426⟩,
  ⟨136,56,[-1],423⟩,
  ⟨136,57,[-1],423⟩,
  ⟨136,58,[-1],423⟩,
  ⟨136,59,[-1],423⟩,
  ⟨136,60,[-1],443⟩,
  ⟨136,61,[-1],434⟩,
  ⟨136,62,[-1],438⟩,
  ⟨136,63,[-1],453⟩
]

private theorem goal_subset_135 : ∀ r ∈ goalRecords_135, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_135 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 136)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 136) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_135, r.goal = 136 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_135, r.goal = 136 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_135 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 136)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 136) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 136 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 136 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_135 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_135 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_135 r hr, hg, hb, hp⟩

private def goalRecords_136 : List MiddleCertRecord := [
  ⟨137,0,[-1],224⟩,
  ⟨137,1,[-1],224⟩,
  ⟨137,2,[-1],224⟩,
  ⟨137,3,[-1],224⟩,
  ⟨137,4,[-1],799⟩,
  ⟨137,5,[-1],799⟩,
  ⟨137,6,[-1],799⟩,
  ⟨137,7,[-1],799⟩,
  ⟨137,8,[-1],929⟩,
  ⟨137,9,[-1],1121⟩,
  ⟨137,10,[-1],1193⟩,
  ⟨137,11,[-1],669⟩,
  ⟨137,12,[-1],799⟩,
  ⟨137,13,[-1],799⟩,
  ⟨137,14,[-1],799⟩,
  ⟨137,15,[-1],799⟩,
  ⟨137,16,[-1],1175⟩,
  ⟨137,17,[-1],1175⟩,
  ⟨137,18,[-1],1175⟩,
  ⟨137,19,[-1],1175⟩,
  ⟨137,20,[-1],1175⟩,
  ⟨137,21,[-1],1175⟩,
  ⟨137,22,[-1],1175⟩,
  ⟨137,23,[-1],1175⟩,
  ⟨137,24,[-1],997⟩,
  ⟨137,25,[-1],997⟩,
  ⟨137,26,[-1],997⟩,
  ⟨137,27,[-1],997⟩,
  ⟨137,28,[-1],997⟩,
  ⟨137,29,[-1],997⟩,
  ⟨137,30,[-1],997⟩,
  ⟨137,31,[-1],997⟩,
  ⟨137,32,[-1],224⟩,
  ⟨137,33,[-1],224⟩,
  ⟨137,34,[-1],224⟩,
  ⟨137,35,[-1],224⟩,
  ⟨137,36,[-1],799⟩,
  ⟨137,37,[-1],799⟩,
  ⟨137,38,[-1],799⟩,
  ⟨137,39,[-1],799⟩,
  ⟨137,40,[-1],929⟩,
  ⟨137,41,[-1],1121⟩,
  ⟨137,42,[-1],1193⟩,
  ⟨137,43,[-1],669⟩,
  ⟨137,44,[-1],799⟩,
  ⟨137,45,[-1],799⟩,
  ⟨137,46,[-1],799⟩,
  ⟨137,47,[-1],799⟩,
  ⟨137,48,[-1],1175⟩,
  ⟨137,49,[-1],1175⟩,
  ⟨137,50,[-1],1175⟩,
  ⟨137,51,[-1],1175⟩,
  ⟨137,52,[-1],1175⟩,
  ⟨137,53,[-1],1175⟩,
  ⟨137,54,[-1],1175⟩,
  ⟨137,55,[-1],1175⟩,
  ⟨137,56,[-1],997⟩,
  ⟨137,57,[-1],997⟩,
  ⟨137,58,[-1],997⟩,
  ⟨137,59,[-1],997⟩,
  ⟨137,60,[-1],997⟩,
  ⟨137,61,[-1],997⟩,
  ⟨137,62,[-1],997⟩,
  ⟨137,63,[-1],997⟩
]

private theorem goal_subset_136 : ∀ r ∈ goalRecords_136, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_136 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 137)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 137) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_136, r.goal = 137 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_136, r.goal = 137 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_136 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 137)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 137) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 137 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 137 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_136 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_136 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_136 r hr, hg, hb, hp⟩

private def goalRecords_137 : List MiddleCertRecord := [

]

private theorem goal_subset_137 : ∀ r ∈ goalRecords_137, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_137 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 138)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 138) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_137, r.goal = 138 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_137, r.goal = 138 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_137 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 138)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 138) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 138 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 138 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_137 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_137 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_137 r hr, hg, hb, hp⟩

private def goalRecords_138 : List MiddleCertRecord := [
  ⟨139,0,[-1],419⟩,
  ⟨139,1,[-1],451⟩,
  ⟨139,2,[-1],427⟩,
  ⟨139,3,[-1],454⟩,
  ⟨139,4,[-1],419⟩,
  ⟨139,5,[-1],451⟩,
  ⟨139,6,[-1],436⟩,
  ⟨139,7,[-1],433⟩,
  ⟨139,8,[-1],419⟩,
  ⟨139,9,[-1],451⟩,
  ⟨139,10,[-1],427⟩,
  ⟨139,11,[-1],432⟩,
  ⟨139,12,[-1],419⟩,
  ⟨139,13,[-1],451⟩,
  ⟨139,14,[-1],427⟩,
  ⟨139,15,[-1],447⟩
]

private theorem goal_subset_138 : ∀ r ∈ goalRecords_138, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_138 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 139)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 139) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_138, r.goal = 139 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_138, r.goal = 139 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_138 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 139)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 139) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 139 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 139 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_138 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_138 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_138 r hr, hg, hb, hp⟩

private def goalRecords_139 : List MiddleCertRecord := [
  ⟨140,0,[-1],414⟩,
  ⟨140,1,[-1],441⟩,
  ⟨140,2,[-1],468⟩,
  ⟨140,3,[-1],468⟩,
  ⟨140,4,[-1],414⟩,
  ⟨140,5,[-1],441⟩,
  ⟨140,6,[-1],905⟩,
  ⟨140,7,[-1],614⟩,
  ⟨140,8,[-1],716⟩,
  ⟨140,9,[-1],720⟩,
  ⟨140,10,[-1],719⟩,
  ⟨140,11,[-1],719⟩,
  ⟨140,12,[-1],1163⟩,
  ⟨140,13,[-1],1165⟩,
  ⟨140,14,[-1],1164⟩,
  ⟨140,15,[-1],1164⟩
]

private theorem goal_subset_139 : ∀ r ∈ goalRecords_139, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_139 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 140)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 140) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_139, r.goal = 140 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_139, r.goal = 140 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_139 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 140)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 140) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 140 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 140 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_139 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_139 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_139 r hr, hg, hb, hp⟩

private def goalRecords_140 : List MiddleCertRecord := [

]

private theorem goal_subset_140 : ∀ r ∈ goalRecords_140, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_140 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 141)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 141) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_140, r.goal = 141 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_140, r.goal = 141 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_140 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 141)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 141) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 141 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 141 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_140 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_140 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_140 r hr, hg, hb, hp⟩

private def goalRecords_141 : List MiddleCertRecord := [
  ⟨142,0,[-1],416⟩,
  ⟨142,1,[-1],455⟩,
  ⟨142,2,[-1],420⟩,
  ⟨142,3,[-1],456⟩,
  ⟨142,4,[-1],416⟩,
  ⟨142,5,[-1],455⟩,
  ⟨142,6,[-1],429⟩,
  ⟨142,7,[-1],439⟩,
  ⟨142,8,[-1],416⟩,
  ⟨142,9,[-1],455⟩,
  ⟨142,10,[-1],420⟩,
  ⟨142,11,[-1],428⟩,
  ⟨142,12,[-1],416⟩,
  ⟨142,13,[-1],455⟩,
  ⟨142,14,[-1],420⟩,
  ⟨142,15,[-1],448⟩
]

private theorem goal_subset_141 : ∀ r ∈ goalRecords_141, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_141 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 142)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 142) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_141, r.goal = 142 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_141, r.goal = 142 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_141 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 142)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 142) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 142 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 142 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_141 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_141 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_141 r hr, hg, hb, hp⟩

private def goalRecords_142 : List MiddleCertRecord := [
  ⟨143,0,[-1],8⟩,
  ⟨143,1,[-1],8⟩,
  ⟨143,2,[-1],8⟩,
  ⟨143,3,[-1],8⟩,
  ⟨143,4,[-1],592⟩,
  ⟨143,5,[-1],705⟩,
  ⟨143,6,[-1],599⟩,
  ⟨143,7,[-1],1002⟩,
  ⟨143,8,[-1],763⟩,
  ⟨143,9,[-1],763⟩,
  ⟨143,10,[-1],763⟩,
  ⟨143,11,[-1],763⟩,
  ⟨143,12,[-1],687⟩,
  ⟨143,13,[-1],687⟩,
  ⟨143,14,[-1],687⟩,
  ⟨143,15,[-1],687⟩
]

private theorem goal_subset_142 : ∀ r ∈ goalRecords_142, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_142 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 143)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 143) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_142, r.goal = 143 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_142, r.goal = 143 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_142 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 143)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 143) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 143 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 143 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_142 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_142 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_142 r hr, hg, hb, hp⟩

private def goalRecords_143 : List MiddleCertRecord := [
  ⟨144,0,[-1],415⟩,
  ⟨144,1,[-1],444⟩,
  ⟨144,2,[-1],425⟩,
  ⟨144,3,[-1],417⟩,
  ⟨144,4,[-1],415⟩,
  ⟨144,5,[-1],444⟩,
  ⟨144,6,[-1],425⟩,
  ⟨144,7,[-1],446⟩,
  ⟨144,8,[-1],415⟩,
  ⟨144,9,[-1],444⟩,
  ⟨144,10,[-1],425⟩,
  ⟨144,11,[-1],417⟩,
  ⟨144,12,[-1],415⟩,
  ⟨144,13,[-1],444⟩,
  ⟨144,14,[-1],425⟩,
  ⟨144,15,[-1],431⟩,
  ⟨144,16,[-1],415⟩,
  ⟨144,17,[-1],444⟩,
  ⟨144,18,[-1],425⟩,
  ⟨144,19,[-1],417⟩,
  ⟨144,20,[-1],415⟩,
  ⟨144,21,[-1],444⟩,
  ⟨144,22,[-1],425⟩,
  ⟨144,23,[-1],435⟩,
  ⟨144,24,[-1],1106⟩,
  ⟨144,25,[-1],1111⟩,
  ⟨144,26,[-1],1109⟩,
  ⟨144,27,[-1],1107⟩,
  ⟨144,28,[-1],1106⟩,
  ⟨144,29,[-1],1111⟩,
  ⟨144,30,[-1],1109⟩,
  ⟨144,31,[-1],1113⟩
]

private theorem goal_subset_143 : ∀ r ∈ goalRecords_143, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_143 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 144)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 144) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_143, r.goal = 144 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_143, r.goal = 144 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_143 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 144)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 144) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 144 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 144 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_143 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_143 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_143 r hr, hg, hb, hp⟩

private def goalRecords_144 : List MiddleCertRecord := [

]

private theorem goal_subset_144 : ∀ r ∈ goalRecords_144, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_144 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 145)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 145) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_144, r.goal = 145 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_144, r.goal = 145 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_144 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 145)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 145) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 145 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 145 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_144 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_144 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_144 r hr, hg, hb, hp⟩

private def goalRecords_145 : List MiddleCertRecord := [
  ⟨146,0,[-1],418⟩,
  ⟨146,1,[-1],445⟩,
  ⟨146,2,[-1],417⟩,
  ⟨146,3,[-1],417⟩,
  ⟨146,4,[-1],418⟩,
  ⟨146,5,[-1],445⟩,
  ⟨146,6,[-1],417⟩,
  ⟨146,7,[-1],417⟩,
  ⟨146,8,[-1],418⟩,
  ⟨146,9,[-1],445⟩,
  ⟨146,10,[-1],417⟩,
  ⟨146,11,[-1],417⟩,
  ⟨146,12,[-1],418⟩,
  ⟨146,13,[-1],445⟩,
  ⟨146,14,[-1],417⟩,
  ⟨146,15,[-1],417⟩,
  ⟨146,16,[-1],418⟩,
  ⟨146,17,[-1],445⟩,
  ⟨146,18,[-1],417⟩,
  ⟨146,19,[-1],417⟩,
  ⟨146,20,[-1],418⟩,
  ⟨146,21,[-1],445⟩,
  ⟨146,22,[-1],417⟩,
  ⟨146,23,[-1],417⟩,
  ⟨146,24,[-1],418⟩,
  ⟨146,25,[-1],445⟩,
  ⟨146,26,[-1],417⟩,
  ⟨146,27,[-1],417⟩,
  ⟨146,28,[-1],418⟩,
  ⟨146,29,[-1],445⟩,
  ⟨146,30,[-1],417⟩,
  ⟨146,31,[-1],417⟩,
  ⟨146,32,[-1],418⟩,
  ⟨146,33,[-1],445⟩,
  ⟨146,34,[-1],422⟩,
  ⟨146,35,[-1],452⟩,
  ⟨146,36,[-1],418⟩,
  ⟨146,37,[-1],445⟩,
  ⟨146,38,[-1],422⟩,
  ⟨146,39,[-1],452⟩,
  ⟨146,40,[-1],418⟩,
  ⟨146,41,[-1],445⟩,
  ⟨146,42,[-1],422⟩,
  ⟨146,43,[-1],437⟩,
  ⟨146,44,[-1],418⟩,
  ⟨146,45,[-1],445⟩,
  ⟨146,46,[-1],422⟩,
  ⟨146,47,[-1],437⟩,
  ⟨146,48,[-1],418⟩,
  ⟨146,49,[-1],445⟩,
  ⟨146,50,[-1],422⟩,
  ⟨146,51,[-1],440⟩,
  ⟨146,52,[-1],418⟩,
  ⟨146,53,[-1],445⟩,
  ⟨146,54,[-1],422⟩,
  ⟨146,55,[-1],440⟩,
  ⟨146,56,[-1],418⟩,
  ⟨146,57,[-1],445⟩,
  ⟨146,58,[-1],422⟩,
  ⟨146,59,[-1],442⟩,
  ⟨146,60,[-1],418⟩,
  ⟨146,61,[-1],445⟩,
  ⟨146,62,[-1],422⟩,
  ⟨146,63,[-1],442⟩
]

private theorem goal_subset_145 : ∀ r ∈ goalRecords_145, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_145 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 146)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 146) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_145, r.goal = 146 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_145, r.goal = 146 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_145 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 146)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 146) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 146 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 146 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_145 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_145 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_145 r hr, hg, hb, hp⟩

private def goalRecords_146 : List MiddleCertRecord := [

]

private theorem goal_subset_146 : ∀ r ∈ goalRecords_146, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_146 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 147)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 147) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_146, r.goal = 147 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_146, r.goal = 147 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_146 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 147)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 147) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 147 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 147 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_146 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_146 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_146 r hr, hg, hb, hp⟩

private def goalRecords_147 : List MiddleCertRecord := [
  ⟨148,0,[-1],1123⟩,
  ⟨148,1,[-1],1177⟩,
  ⟨148,2,[-1],1012⟩,
  ⟨148,3,[-1],899⟩,
  ⟨148,4,[-1],664⟩,
  ⟨148,5,[-1],1018⟩,
  ⟨148,6,[-1],1115⟩,
  ⟨148,7,[-1],1118⟩,
  ⟨148,8,[-1],754⟩,
  ⟨148,9,[-1],758⟩,
  ⟨148,10,[-1],755⟩,
  ⟨148,11,[-1],755⟩,
  ⟨148,12,[-1],1146⟩,
  ⟨148,13,[-1],1148⟩,
  ⟨148,14,[-1],1146⟩,
  ⟨148,15,[-1],1146⟩
]

private theorem goal_subset_147 : ∀ r ∈ goalRecords_147, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_147 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 148)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 148) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_147, r.goal = 148 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_147, r.goal = 148 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_147 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 148)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 148) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 148 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 148 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_147 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_147 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_147 r hr, hg, hb, hp⟩

private def goalRecords_148 : List MiddleCertRecord := [
  ⟨149,8,[-1],457⟩,
  ⟨149,9,[-1],430⟩,
  ⟨149,10,[-1],756⟩,
  ⟨149,11,[-1],1153⟩
]

private theorem goal_subset_148 : ∀ r ∈ goalRecords_148, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_148 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 149)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 149) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_148, r.goal = 149 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ goalRecords_148, r.goal = 149 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_148 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 149)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 149) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 149 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = 149 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_148 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_148 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_148 r hr, hg, hb, hp⟩

private theorem coverage :
    ∀ i ∈ selectedGoals,
      ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData (i+1))).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData (i+1)) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (8 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 8)).length,
          ∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents)  := by
  simp only [selectedGoals, List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨cover_132, cover_133, cover_134, cover_135, cover_136, cover_137, cover_138, cover_139, cover_140, cover_141, cover_142, cover_143, cover_144, cover_145, cover_146, cover_147, cover_148, List.forall_mem_nil _⟩

end FastFamily8

open FastFamily8

theorem solution : middleCertFamilyValid middleCertData 8 := by
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
