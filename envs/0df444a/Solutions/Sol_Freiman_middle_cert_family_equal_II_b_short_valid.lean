-- Prove2me | solution 1 for Freiman.middle_cert_family_equal_II_b_short_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:09:11.673186+00:00
-- url     : https://prove2.me/submissions/d30948cd-80df-411a-b57f-de476c02c71c

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

namespace FastFamily7

private def selectedRecords : List MiddleCertRecord := [
  ⟨118,0,[-1],421⟩,
  ⟨118,1,[-1],803⟩,
  ⟨118,2,[-1],1096⟩,
  ⟨118,4,[-1],395⟩,
  ⟨118,5,[-1],395⟩,
  ⟨118,6,[-1],395⟩,
  ⟨118,7,[-1],395⟩,
  ⟨118,8,[-1],739⟩,
  ⟨118,9,[-1],739⟩,
  ⟨118,10,[-1],739⟩,
  ⟨118,11,[-1],739⟩,
  ⟨118,12,[-1],739⟩,
  ⟨118,13,[-1],739⟩,
  ⟨118,14,[-1],739⟩,
  ⟨118,15,[-1],739⟩,
  ⟨119,1,[-1],407⟩,
  ⟨119,2,[-1],739⟩,
  ⟨119,3,[-1],739⟩,
  ⟨119,7,[-1],739⟩,
  ⟨119,8,[-1],745⟩,
  ⟨119,9,[-1],745⟩,
  ⟨119,11,[-1],1137⟩,
  ⟨119,13,[-1],1138⟩,
  ⟨119,17,[-1],407⟩,
  ⟨119,18,[-1],739⟩,
  ⟨119,19,[-1],739⟩,
  ⟨119,23,[-1],739⟩,
  ⟨119,24,[-1],744⟩,
  ⟨119,25,[-1],744⟩,
  ⟨119,27,[-1],1137⟩,
  ⟨119,29,[-1],1136⟩,
  ⟨121,0,[-1],359⟩,
  ⟨121,1,[-1],359⟩,
  ⟨121,2,[-1],359⟩,
  ⟨121,3,[-1],359⟩,
  ⟨121,4,[-1],359⟩,
  ⟨121,5,[-1],359⟩,
  ⟨121,6,[-1],359⟩,
  ⟨121,7,[-1],359⟩,
  ⟨121,8,[-1],396⟩,
  ⟨121,9,[-1],396⟩,
  ⟨121,10,[-1],396⟩,
  ⟨121,11,[-1],396⟩,
  ⟨121,12,[-1],396⟩,
  ⟨121,13,[-1],396⟩,
  ⟨121,14,[-1],396⟩,
  ⟨121,15,[-1],396⟩,
  ⟨121,16,[-1],356⟩,
  ⟨121,17,[-1],356⟩,
  ⟨121,18,[-1],356⟩,
  ⟨121,19,[-1],356⟩,
  ⟨121,20,[-1],361⟩,
  ⟨121,21,[-1],361⟩,
  ⟨121,22,[-1],361⟩,
  ⟨121,23,[-1],361⟩,
  ⟨121,24,[-1],356⟩,
  ⟨121,25,[-1],356⟩,
  ⟨121,26,[-1],356⟩,
  ⟨121,27,[-1],356⟩,
  ⟨121,28,[-1],385⟩,
  ⟨121,29,[-1],370⟩,
  ⟨121,30,[-1],375⟩,
  ⟨121,31,[-1],400⟩,
  ⟨121,32,[-1],359⟩,
  ⟨121,33,[-1],359⟩,
  ⟨121,34,[-1],359⟩,
  ⟨121,35,[-1],359⟩,
  ⟨121,36,[-1],359⟩,
  ⟨121,37,[-1],359⟩,
  ⟨121,38,[-1],359⟩,
  ⟨121,39,[-1],359⟩,
  ⟨121,40,[-1],396⟩,
  ⟨121,41,[-1],396⟩,
  ⟨121,42,[-1],396⟩,
  ⟨121,43,[-1],396⟩,
  ⟨121,44,[-1],396⟩,
  ⟨121,45,[-1],396⟩,
  ⟨121,46,[-1],396⟩,
  ⟨121,47,[-1],396⟩,
  ⟨121,48,[-1],356⟩,
  ⟨121,49,[-1],356⟩,
  ⟨121,50,[-1],356⟩,
  ⟨121,51,[-1],356⟩,
  ⟨121,52,[-1],361⟩,
  ⟨121,53,[-1],361⟩,
  ⟨121,54,[-1],361⟩,
  ⟨121,55,[-1],361⟩,
  ⟨121,56,[-1],356⟩,
  ⟨121,57,[-1],356⟩,
  ⟨121,58,[-1],356⟩,
  ⟨121,59,[-1],356⟩,
  ⟨121,60,[-1],385⟩,
  ⟨121,61,[-1],370⟩,
  ⟨121,62,[-1],375⟩,
  ⟨121,63,[-1],400⟩,
  ⟨122,0,[-1],224⟩,
  ⟨122,1,[-1],224⟩,
  ⟨122,2,[-1],224⟩,
  ⟨122,3,[-1],224⟩,
  ⟨122,4,[-1],799⟩,
  ⟨122,5,[-1],799⟩,
  ⟨122,6,[-1],799⟩,
  ⟨122,7,[-1],799⟩,
  ⟨122,8,[-1],929⟩,
  ⟨122,9,[-1],1121⟩,
  ⟨122,10,[-1],1193⟩,
  ⟨122,11,[-1],669⟩,
  ⟨122,12,[-1],799⟩,
  ⟨122,13,[-1],799⟩,
  ⟨122,14,[-1],799⟩,
  ⟨122,15,[-1],799⟩,
  ⟨122,16,[-1],1175⟩,
  ⟨122,17,[-1],1175⟩,
  ⟨122,18,[-1],1175⟩,
  ⟨122,19,[-1],1175⟩,
  ⟨122,20,[-1],1175⟩,
  ⟨122,21,[-1],1175⟩,
  ⟨122,22,[-1],1175⟩,
  ⟨122,23,[-1],1175⟩,
  ⟨122,24,[-1],997⟩,
  ⟨122,25,[-1],997⟩,
  ⟨122,26,[-1],997⟩,
  ⟨122,27,[-1],997⟩,
  ⟨122,28,[-1],997⟩,
  ⟨122,29,[-1],997⟩,
  ⟨122,30,[-1],997⟩,
  ⟨122,31,[-1],997⟩,
  ⟨122,32,[-1],224⟩,
  ⟨122,33,[-1],224⟩,
  ⟨122,34,[-1],224⟩,
  ⟨122,35,[-1],224⟩,
  ⟨122,36,[-1],799⟩,
  ⟨122,37,[-1],799⟩,
  ⟨122,38,[-1],799⟩,
  ⟨122,39,[-1],799⟩,
  ⟨122,40,[-1],929⟩,
  ⟨122,41,[-1],1121⟩,
  ⟨122,42,[-1],1193⟩,
  ⟨122,43,[-1],669⟩,
  ⟨122,44,[-1],799⟩,
  ⟨122,45,[-1],799⟩,
  ⟨122,46,[-1],799⟩,
  ⟨122,47,[-1],799⟩,
  ⟨122,48,[-1],1175⟩,
  ⟨122,49,[-1],1175⟩,
  ⟨122,50,[-1],1175⟩,
  ⟨122,51,[-1],1175⟩,
  ⟨122,52,[-1],1175⟩,
  ⟨122,53,[-1],1175⟩,
  ⟨122,54,[-1],1175⟩,
  ⟨122,55,[-1],1175⟩,
  ⟨122,56,[-1],997⟩,
  ⟨122,57,[-1],997⟩,
  ⟨122,58,[-1],997⟩,
  ⟨122,59,[-1],997⟩,
  ⟨122,60,[-1],997⟩,
  ⟨122,61,[-1],997⟩,
  ⟨122,62,[-1],997⟩,
  ⟨122,63,[-1],997⟩,
  ⟨124,0,[-1],348⟩,
  ⟨124,1,[-1],397⟩,
  ⟨124,2,[-1],362⟩,
  ⟨124,3,[-1],402⟩,
  ⟨124,4,[-1],348⟩,
  ⟨124,5,[-1],397⟩,
  ⟨124,6,[-1],373⟩,
  ⟨124,7,[-1],368⟩,
  ⟨124,8,[-1],348⟩,
  ⟨124,9,[-1],397⟩,
  ⟨124,10,[-1],362⟩,
  ⟨124,11,[-1],367⟩,
  ⟨124,12,[-1],348⟩,
  ⟨124,13,[-1],397⟩,
  ⟨124,14,[-1],362⟩,
  ⟨124,15,[-1],392⟩,
  ⟨125,0,[-1],414⟩,
  ⟨125,1,[-1],380⟩,
  ⟨125,2,[-1],468⟩,
  ⟨125,3,[-1],468⟩,
  ⟨125,4,[-1],414⟩,
  ⟨125,5,[-1],380⟩,
  ⟨125,6,[-1],905⟩,
  ⟨125,7,[-1],614⟩,
  ⟨125,8,[-1],716⟩,
  ⟨125,9,[-1],720⟩,
  ⟨125,10,[-1],719⟩,
  ⟨125,11,[-1],719⟩,
  ⟨125,12,[-1],1163⟩,
  ⟨125,13,[-1],1165⟩,
  ⟨125,14,[-1],1164⟩,
  ⟨125,15,[-1],1164⟩,
  ⟨127,0,[-1],345⟩,
  ⟨127,1,[-1],403⟩,
  ⟨127,2,[-1],350⟩,
  ⟨127,3,[-1],404⟩,
  ⟨127,4,[-1],345⟩,
  ⟨127,5,[-1],403⟩,
  ⟨127,6,[-1],364⟩,
  ⟨127,7,[-1],377⟩,
  ⟨127,8,[-1],345⟩,
  ⟨127,9,[-1],403⟩,
  ⟨127,10,[-1],350⟩,
  ⟨127,11,[-1],363⟩,
  ⟨127,12,[-1],345⟩,
  ⟨127,13,[-1],403⟩,
  ⟨127,14,[-1],350⟩,
  ⟨127,15,[-1],393⟩,
  ⟨128,0,[-1],8⟩,
  ⟨128,1,[-1],8⟩,
  ⟨128,2,[-1],8⟩,
  ⟨128,3,[-1],8⟩,
  ⟨128,4,[-1],592⟩,
  ⟨128,5,[-1],705⟩,
  ⟨128,6,[-1],599⟩,
  ⟨128,7,[-1],1002⟩,
  ⟨128,8,[-1],763⟩,
  ⟨128,9,[-1],763⟩,
  ⟨128,10,[-1],763⟩,
  ⟨128,11,[-1],763⟩,
  ⟨128,12,[-1],687⟩,
  ⟨128,13,[-1],687⟩,
  ⟨128,14,[-1],687⟩,
  ⟨128,15,[-1],687⟩,
  ⟨129,0,[-1],344⟩,
  ⟨129,1,[-1],387⟩,
  ⟨129,2,[-1],360⟩,
  ⟨129,3,[-1],346⟩,
  ⟨129,4,[-1],344⟩,
  ⟨129,5,[-1],387⟩,
  ⟨129,6,[-1],360⟩,
  ⟨129,7,[-1],391⟩,
  ⟨129,8,[-1],344⟩,
  ⟨129,9,[-1],387⟩,
  ⟨129,10,[-1],360⟩,
  ⟨129,11,[-1],346⟩,
  ⟨129,12,[-1],344⟩,
  ⟨129,13,[-1],387⟩,
  ⟨129,14,[-1],360⟩,
  ⟨129,15,[-1],366⟩,
  ⟨129,16,[-1],344⟩,
  ⟨129,17,[-1],387⟩,
  ⟨129,18,[-1],360⟩,
  ⟨129,19,[-1],346⟩,
  ⟨129,20,[-1],344⟩,
  ⟨129,21,[-1],387⟩,
  ⟨129,22,[-1],360⟩,
  ⟨129,23,[-1],371⟩,
  ⟨129,24,[-1],344⟩,
  ⟨129,25,[-1],387⟩,
  ⟨129,26,[-1],360⟩,
  ⟨129,27,[-1],346⟩,
  ⟨129,28,[-1],344⟩,
  ⟨129,29,[-1],387⟩,
  ⟨129,30,[-1],360⟩,
  ⟨129,31,[-1],394⟩,
  ⟨131,0,[-1],347⟩,
  ⟨131,1,[-1],389⟩,
  ⟨131,2,[-1],346⟩,
  ⟨131,3,[-1],346⟩,
  ⟨131,4,[-1],347⟩,
  ⟨131,5,[-1],389⟩,
  ⟨131,6,[-1],346⟩,
  ⟨131,7,[-1],346⟩,
  ⟨131,8,[-1],347⟩,
  ⟨131,9,[-1],389⟩,
  ⟨131,10,[-1],346⟩,
  ⟨131,11,[-1],346⟩,
  ⟨131,12,[-1],347⟩,
  ⟨131,13,[-1],389⟩,
  ⟨131,14,[-1],346⟩,
  ⟨131,15,[-1],346⟩,
  ⟨131,16,[-1],347⟩,
  ⟨131,17,[-1],389⟩,
  ⟨131,18,[-1],346⟩,
  ⟨131,19,[-1],346⟩,
  ⟨131,20,[-1],347⟩,
  ⟨131,21,[-1],389⟩,
  ⟨131,22,[-1],346⟩,
  ⟨131,23,[-1],346⟩,
  ⟨131,24,[-1],347⟩,
  ⟨131,25,[-1],389⟩,
  ⟨131,26,[-1],346⟩,
  ⟨131,27,[-1],346⟩,
  ⟨131,28,[-1],347⟩,
  ⟨131,29,[-1],389⟩,
  ⟨131,30,[-1],346⟩,
  ⟨131,31,[-1],346⟩,
  ⟨131,32,[-1],347⟩,
  ⟨131,33,[-1],389⟩,
  ⟨131,34,[-1],354⟩,
  ⟨131,35,[-1],398⟩,
  ⟨131,36,[-1],347⟩,
  ⟨131,37,[-1],389⟩,
  ⟨131,38,[-1],354⟩,
  ⟨131,39,[-1],398⟩,
  ⟨131,40,[-1],347⟩,
  ⟨131,41,[-1],389⟩,
  ⟨131,42,[-1],354⟩,
  ⟨131,43,[-1],374⟩,
  ⟨131,44,[-1],347⟩,
  ⟨131,45,[-1],389⟩,
  ⟨131,46,[-1],354⟩,
  ⟨131,47,[-1],374⟩,
  ⟨131,48,[-1],347⟩,
  ⟨131,49,[-1],389⟩,
  ⟨131,50,[-1],354⟩,
  ⟨131,51,[-1],378⟩,
  ⟨131,52,[-1],347⟩,
  ⟨131,53,[-1],389⟩,
  ⟨131,54,[-1],354⟩,
  ⟨131,55,[-1],378⟩,
  ⟨131,56,[-1],347⟩,
  ⟨131,57,[-1],389⟩,
  ⟨131,58,[-1],354⟩,
  ⟨131,59,[-1],382⟩,
  ⟨131,60,[-1],347⟩,
  ⟨131,61,[-1],389⟩,
  ⟨131,62,[-1],354⟩,
  ⟨131,63,[-1],382⟩
]

private def selectedGoals : List ℕ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]

private theorem records_eq :
    middleCertData.records.filter (fun r => decide ((middleCertGoal middleCertData r.goal).family = 7)) = selectedRecords := by
  decide +kernel

private theorem goals_eq :
    (List.range middleCertData.goals.length).filter (fun i => decide ((middleCertGoal middleCertData (i+1)).family = 7)) = selectedGoals := by
  decide +kernel

private def chunk_0 : List MiddleCertRecord := [
  ⟨118,0,[-1],421⟩,
  ⟨118,1,[-1],803⟩,
  ⟨118,2,[-1],1096⟩,
  ⟨118,4,[-1],395⟩,
  ⟨118,5,[-1],395⟩,
  ⟨118,6,[-1],395⟩,
  ⟨118,7,[-1],395⟩,
  ⟨118,8,[-1],739⟩,
  ⟨118,9,[-1],739⟩,
  ⟨118,10,[-1],739⟩,
  ⟨118,11,[-1],739⟩,
  ⟨118,12,[-1],739⟩,
  ⟨118,13,[-1],739⟩,
  ⟨118,14,[-1],739⟩,
  ⟨118,15,[-1],739⟩,
  ⟨119,1,[-1],407⟩
]

private theorem chunk_valid_0 : ∀ r ∈ chunk_0, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨119,2,[-1],739⟩,
  ⟨119,3,[-1],739⟩,
  ⟨119,7,[-1],739⟩,
  ⟨119,8,[-1],745⟩,
  ⟨119,9,[-1],745⟩,
  ⟨119,11,[-1],1137⟩,
  ⟨119,13,[-1],1138⟩,
  ⟨119,17,[-1],407⟩,
  ⟨119,18,[-1],739⟩,
  ⟨119,19,[-1],739⟩,
  ⟨119,23,[-1],739⟩,
  ⟨119,24,[-1],744⟩,
  ⟨119,25,[-1],744⟩,
  ⟨119,27,[-1],1137⟩,
  ⟨119,29,[-1],1136⟩,
  ⟨121,0,[-1],359⟩
]

private theorem chunk_valid_1 : ∀ r ∈ chunk_1, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨121,1,[-1],359⟩,
  ⟨121,2,[-1],359⟩,
  ⟨121,3,[-1],359⟩,
  ⟨121,4,[-1],359⟩,
  ⟨121,5,[-1],359⟩,
  ⟨121,6,[-1],359⟩,
  ⟨121,7,[-1],359⟩,
  ⟨121,8,[-1],396⟩,
  ⟨121,9,[-1],396⟩,
  ⟨121,10,[-1],396⟩,
  ⟨121,11,[-1],396⟩,
  ⟨121,12,[-1],396⟩,
  ⟨121,13,[-1],396⟩,
  ⟨121,14,[-1],396⟩,
  ⟨121,15,[-1],396⟩,
  ⟨121,16,[-1],356⟩
]

private theorem chunk_valid_2 : ∀ r ∈ chunk_2, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨121,17,[-1],356⟩,
  ⟨121,18,[-1],356⟩,
  ⟨121,19,[-1],356⟩,
  ⟨121,20,[-1],361⟩,
  ⟨121,21,[-1],361⟩,
  ⟨121,22,[-1],361⟩,
  ⟨121,23,[-1],361⟩,
  ⟨121,24,[-1],356⟩,
  ⟨121,25,[-1],356⟩,
  ⟨121,26,[-1],356⟩,
  ⟨121,27,[-1],356⟩,
  ⟨121,28,[-1],385⟩,
  ⟨121,29,[-1],370⟩,
  ⟨121,30,[-1],375⟩,
  ⟨121,31,[-1],400⟩,
  ⟨121,32,[-1],359⟩
]

private theorem chunk_valid_3 : ∀ r ∈ chunk_3, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨121,33,[-1],359⟩,
  ⟨121,34,[-1],359⟩,
  ⟨121,35,[-1],359⟩,
  ⟨121,36,[-1],359⟩,
  ⟨121,37,[-1],359⟩,
  ⟨121,38,[-1],359⟩,
  ⟨121,39,[-1],359⟩,
  ⟨121,40,[-1],396⟩,
  ⟨121,41,[-1],396⟩,
  ⟨121,42,[-1],396⟩,
  ⟨121,43,[-1],396⟩,
  ⟨121,44,[-1],396⟩,
  ⟨121,45,[-1],396⟩,
  ⟨121,46,[-1],396⟩,
  ⟨121,47,[-1],396⟩,
  ⟨121,48,[-1],356⟩
]

private theorem chunk_valid_4 : ∀ r ∈ chunk_4, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨121,49,[-1],356⟩,
  ⟨121,50,[-1],356⟩,
  ⟨121,51,[-1],356⟩,
  ⟨121,52,[-1],361⟩,
  ⟨121,53,[-1],361⟩,
  ⟨121,54,[-1],361⟩,
  ⟨121,55,[-1],361⟩,
  ⟨121,56,[-1],356⟩,
  ⟨121,57,[-1],356⟩,
  ⟨121,58,[-1],356⟩,
  ⟨121,59,[-1],356⟩,
  ⟨121,60,[-1],385⟩,
  ⟨121,61,[-1],370⟩,
  ⟨121,62,[-1],375⟩,
  ⟨121,63,[-1],400⟩,
  ⟨122,0,[-1],224⟩
]

private theorem chunk_valid_5 : ∀ r ∈ chunk_5, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨122,1,[-1],224⟩,
  ⟨122,2,[-1],224⟩,
  ⟨122,3,[-1],224⟩,
  ⟨122,4,[-1],799⟩,
  ⟨122,5,[-1],799⟩,
  ⟨122,6,[-1],799⟩,
  ⟨122,7,[-1],799⟩,
  ⟨122,8,[-1],929⟩,
  ⟨122,9,[-1],1121⟩,
  ⟨122,10,[-1],1193⟩,
  ⟨122,11,[-1],669⟩,
  ⟨122,12,[-1],799⟩,
  ⟨122,13,[-1],799⟩,
  ⟨122,14,[-1],799⟩,
  ⟨122,15,[-1],799⟩,
  ⟨122,16,[-1],1175⟩
]

private theorem chunk_valid_6 : ∀ r ∈ chunk_6, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨122,17,[-1],1175⟩,
  ⟨122,18,[-1],1175⟩,
  ⟨122,19,[-1],1175⟩,
  ⟨122,20,[-1],1175⟩,
  ⟨122,21,[-1],1175⟩,
  ⟨122,22,[-1],1175⟩,
  ⟨122,23,[-1],1175⟩,
  ⟨122,24,[-1],997⟩,
  ⟨122,25,[-1],997⟩,
  ⟨122,26,[-1],997⟩,
  ⟨122,27,[-1],997⟩,
  ⟨122,28,[-1],997⟩,
  ⟨122,29,[-1],997⟩,
  ⟨122,30,[-1],997⟩,
  ⟨122,31,[-1],997⟩,
  ⟨122,32,[-1],224⟩
]

private theorem chunk_valid_7 : ∀ r ∈ chunk_7, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨122,33,[-1],224⟩,
  ⟨122,34,[-1],224⟩,
  ⟨122,35,[-1],224⟩,
  ⟨122,36,[-1],799⟩,
  ⟨122,37,[-1],799⟩,
  ⟨122,38,[-1],799⟩,
  ⟨122,39,[-1],799⟩,
  ⟨122,40,[-1],929⟩,
  ⟨122,41,[-1],1121⟩,
  ⟨122,42,[-1],1193⟩,
  ⟨122,43,[-1],669⟩,
  ⟨122,44,[-1],799⟩,
  ⟨122,45,[-1],799⟩,
  ⟨122,46,[-1],799⟩,
  ⟨122,47,[-1],799⟩,
  ⟨122,48,[-1],1175⟩
]

private theorem chunk_valid_8 : ∀ r ∈ chunk_8, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨122,49,[-1],1175⟩,
  ⟨122,50,[-1],1175⟩,
  ⟨122,51,[-1],1175⟩,
  ⟨122,52,[-1],1175⟩,
  ⟨122,53,[-1],1175⟩,
  ⟨122,54,[-1],1175⟩,
  ⟨122,55,[-1],1175⟩,
  ⟨122,56,[-1],997⟩,
  ⟨122,57,[-1],997⟩,
  ⟨122,58,[-1],997⟩,
  ⟨122,59,[-1],997⟩,
  ⟨122,60,[-1],997⟩,
  ⟨122,61,[-1],997⟩,
  ⟨122,62,[-1],997⟩,
  ⟨122,63,[-1],997⟩,
  ⟨124,0,[-1],348⟩
]

private theorem chunk_valid_9 : ∀ r ∈ chunk_9, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨124,1,[-1],397⟩,
  ⟨124,2,[-1],362⟩,
  ⟨124,3,[-1],402⟩,
  ⟨124,4,[-1],348⟩,
  ⟨124,5,[-1],397⟩,
  ⟨124,6,[-1],373⟩,
  ⟨124,7,[-1],368⟩,
  ⟨124,8,[-1],348⟩,
  ⟨124,9,[-1],397⟩,
  ⟨124,10,[-1],362⟩,
  ⟨124,11,[-1],367⟩,
  ⟨124,12,[-1],348⟩,
  ⟨124,13,[-1],397⟩,
  ⟨124,14,[-1],362⟩,
  ⟨124,15,[-1],392⟩,
  ⟨125,0,[-1],414⟩
]

private theorem chunk_valid_10 : ∀ r ∈ chunk_10, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨125,1,[-1],380⟩,
  ⟨125,2,[-1],468⟩,
  ⟨125,3,[-1],468⟩,
  ⟨125,4,[-1],414⟩,
  ⟨125,5,[-1],380⟩,
  ⟨125,6,[-1],905⟩,
  ⟨125,7,[-1],614⟩,
  ⟨125,8,[-1],716⟩,
  ⟨125,9,[-1],720⟩,
  ⟨125,10,[-1],719⟩,
  ⟨125,11,[-1],719⟩,
  ⟨125,12,[-1],1163⟩,
  ⟨125,13,[-1],1165⟩,
  ⟨125,14,[-1],1164⟩,
  ⟨125,15,[-1],1164⟩,
  ⟨127,0,[-1],345⟩
]

private theorem chunk_valid_11 : ∀ r ∈ chunk_11, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨127,1,[-1],403⟩,
  ⟨127,2,[-1],350⟩,
  ⟨127,3,[-1],404⟩,
  ⟨127,4,[-1],345⟩,
  ⟨127,5,[-1],403⟩,
  ⟨127,6,[-1],364⟩,
  ⟨127,7,[-1],377⟩,
  ⟨127,8,[-1],345⟩,
  ⟨127,9,[-1],403⟩,
  ⟨127,10,[-1],350⟩,
  ⟨127,11,[-1],363⟩,
  ⟨127,12,[-1],345⟩,
  ⟨127,13,[-1],403⟩,
  ⟨127,14,[-1],350⟩,
  ⟨127,15,[-1],393⟩,
  ⟨128,0,[-1],8⟩
]

private theorem chunk_valid_12 : ∀ r ∈ chunk_12, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨128,1,[-1],8⟩,
  ⟨128,2,[-1],8⟩,
  ⟨128,3,[-1],8⟩,
  ⟨128,4,[-1],592⟩,
  ⟨128,5,[-1],705⟩,
  ⟨128,6,[-1],599⟩,
  ⟨128,7,[-1],1002⟩,
  ⟨128,8,[-1],763⟩,
  ⟨128,9,[-1],763⟩,
  ⟨128,10,[-1],763⟩,
  ⟨128,11,[-1],763⟩,
  ⟨128,12,[-1],687⟩,
  ⟨128,13,[-1],687⟩,
  ⟨128,14,[-1],687⟩,
  ⟨128,15,[-1],687⟩,
  ⟨129,0,[-1],344⟩
]

private theorem chunk_valid_13 : ∀ r ∈ chunk_13, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨129,1,[-1],387⟩,
  ⟨129,2,[-1],360⟩,
  ⟨129,3,[-1],346⟩,
  ⟨129,4,[-1],344⟩,
  ⟨129,5,[-1],387⟩,
  ⟨129,6,[-1],360⟩,
  ⟨129,7,[-1],391⟩,
  ⟨129,8,[-1],344⟩,
  ⟨129,9,[-1],387⟩,
  ⟨129,10,[-1],360⟩,
  ⟨129,11,[-1],346⟩,
  ⟨129,12,[-1],344⟩,
  ⟨129,13,[-1],387⟩,
  ⟨129,14,[-1],360⟩,
  ⟨129,15,[-1],366⟩,
  ⟨129,16,[-1],344⟩
]

private theorem chunk_valid_14 : ∀ r ∈ chunk_14, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨129,17,[-1],387⟩,
  ⟨129,18,[-1],360⟩,
  ⟨129,19,[-1],346⟩,
  ⟨129,20,[-1],344⟩,
  ⟨129,21,[-1],387⟩,
  ⟨129,22,[-1],360⟩,
  ⟨129,23,[-1],371⟩,
  ⟨129,24,[-1],344⟩,
  ⟨129,25,[-1],387⟩,
  ⟨129,26,[-1],360⟩,
  ⟨129,27,[-1],346⟩,
  ⟨129,28,[-1],344⟩,
  ⟨129,29,[-1],387⟩,
  ⟨129,30,[-1],360⟩,
  ⟨129,31,[-1],394⟩,
  ⟨131,0,[-1],347⟩
]

private theorem chunk_valid_15 : ∀ r ∈ chunk_15, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨131,1,[-1],389⟩,
  ⟨131,2,[-1],346⟩,
  ⟨131,3,[-1],346⟩,
  ⟨131,4,[-1],347⟩,
  ⟨131,5,[-1],389⟩,
  ⟨131,6,[-1],346⟩,
  ⟨131,7,[-1],346⟩,
  ⟨131,8,[-1],347⟩,
  ⟨131,9,[-1],389⟩,
  ⟨131,10,[-1],346⟩,
  ⟨131,11,[-1],346⟩,
  ⟨131,12,[-1],347⟩,
  ⟨131,13,[-1],389⟩,
  ⟨131,14,[-1],346⟩,
  ⟨131,15,[-1],346⟩,
  ⟨131,16,[-1],347⟩
]

private theorem chunk_valid_16 : ∀ r ∈ chunk_16, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨131,17,[-1],389⟩,
  ⟨131,18,[-1],346⟩,
  ⟨131,19,[-1],346⟩,
  ⟨131,20,[-1],347⟩,
  ⟨131,21,[-1],389⟩,
  ⟨131,22,[-1],346⟩,
  ⟨131,23,[-1],346⟩,
  ⟨131,24,[-1],347⟩,
  ⟨131,25,[-1],389⟩,
  ⟨131,26,[-1],346⟩,
  ⟨131,27,[-1],346⟩,
  ⟨131,28,[-1],347⟩,
  ⟨131,29,[-1],389⟩,
  ⟨131,30,[-1],346⟩,
  ⟨131,31,[-1],346⟩,
  ⟨131,32,[-1],347⟩
]

private theorem chunk_valid_17 : ∀ r ∈ chunk_17, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_18 : List MiddleCertRecord := [
  ⟨131,33,[-1],389⟩,
  ⟨131,34,[-1],354⟩,
  ⟨131,35,[-1],398⟩,
  ⟨131,36,[-1],347⟩,
  ⟨131,37,[-1],389⟩,
  ⟨131,38,[-1],354⟩,
  ⟨131,39,[-1],398⟩,
  ⟨131,40,[-1],347⟩,
  ⟨131,41,[-1],389⟩,
  ⟨131,42,[-1],354⟩,
  ⟨131,43,[-1],374⟩,
  ⟨131,44,[-1],347⟩,
  ⟨131,45,[-1],389⟩,
  ⟨131,46,[-1],354⟩,
  ⟨131,47,[-1],374⟩,
  ⟨131,48,[-1],347⟩
]

private theorem chunk_valid_18 : ∀ r ∈ chunk_18, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_19 : List MiddleCertRecord := [
  ⟨131,49,[-1],389⟩,
  ⟨131,50,[-1],354⟩,
  ⟨131,51,[-1],378⟩,
  ⟨131,52,[-1],347⟩,
  ⟨131,53,[-1],389⟩,
  ⟨131,54,[-1],354⟩,
  ⟨131,55,[-1],378⟩,
  ⟨131,56,[-1],347⟩,
  ⟨131,57,[-1],389⟩,
  ⟨131,58,[-1],354⟩,
  ⟨131,59,[-1],382⟩,
  ⟨131,60,[-1],347⟩,
  ⟨131,61,[-1],389⟩,
  ⟨131,62,[-1],354⟩,
  ⟨131,63,[-1],382⟩
]

private theorem chunk_valid_19 : ∀ r ∈ chunk_19, middleCertRecordValid middleCertData r := by
  decide +kernel

private theorem chunks_eq : [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19].flatten = selectedRecords := by
  decide +kernel

private theorem chunks_valid : ∀ rs ∈ [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19], ∀ r ∈ rs, middleCertRecordValid middleCertData r := by
  simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨chunk_valid_0, chunk_valid_1, chunk_valid_2, chunk_valid_3, chunk_valid_4, chunk_valid_5, chunk_valid_6, chunk_valid_7, chunk_valid_8, chunk_valid_9, chunk_valid_10, chunk_valid_11, chunk_valid_12, chunk_valid_13, chunk_valid_14, chunk_valid_15, chunk_valid_16, chunk_valid_17, chunk_valid_18, chunk_valid_19, List.forall_mem_nil _⟩

private theorem records_valid :
    ∀ r ∈ selectedRecords, middleCertRecordValid middleCertData r := by
  intro r hr
  rw [← chunks_eq] at hr
  rcases List.mem_flatten.mp hr with ⟨rs, hrs, hr⟩
  exact chunks_valid rs hrs r hr

private def goalRecords_117 : List MiddleCertRecord := [
  ⟨118,0,[-1],421⟩,
  ⟨118,1,[-1],803⟩,
  ⟨118,2,[-1],1096⟩,
  ⟨118,4,[-1],395⟩,
  ⟨118,5,[-1],395⟩,
  ⟨118,6,[-1],395⟩,
  ⟨118,7,[-1],395⟩,
  ⟨118,8,[-1],739⟩,
  ⟨118,9,[-1],739⟩,
  ⟨118,10,[-1],739⟩,
  ⟨118,11,[-1],739⟩,
  ⟨118,12,[-1],739⟩,
  ⟨118,13,[-1],739⟩,
  ⟨118,14,[-1],739⟩,
  ⟨118,15,[-1],739⟩
]

private theorem goal_subset_117 : ∀ r ∈ goalRecords_117, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_117 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 118)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 118) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_117, r.goal = 118 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_117, r.goal = 118 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_117 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 118)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 118) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 118 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 118 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_117 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_117 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_117 r hr, hg, hb, hp⟩

private def goalRecords_118 : List MiddleCertRecord := [
  ⟨119,1,[-1],407⟩,
  ⟨119,2,[-1],739⟩,
  ⟨119,3,[-1],739⟩,
  ⟨119,7,[-1],739⟩,
  ⟨119,8,[-1],745⟩,
  ⟨119,9,[-1],745⟩,
  ⟨119,11,[-1],1137⟩,
  ⟨119,13,[-1],1138⟩,
  ⟨119,17,[-1],407⟩,
  ⟨119,18,[-1],739⟩,
  ⟨119,19,[-1],739⟩,
  ⟨119,23,[-1],739⟩,
  ⟨119,24,[-1],744⟩,
  ⟨119,25,[-1],744⟩,
  ⟨119,27,[-1],1137⟩,
  ⟨119,29,[-1],1136⟩
]

private theorem goal_subset_118 : ∀ r ∈ goalRecords_118, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_118 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 119)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 119) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_118, r.goal = 119 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_118, r.goal = 119 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_118 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 119)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 119) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 119 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 119 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_118 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_118 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_118 r hr, hg, hb, hp⟩

private def goalRecords_119 : List MiddleCertRecord := [

]

private theorem goal_subset_119 : ∀ r ∈ goalRecords_119, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_119 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 120)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 120) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_119, r.goal = 120 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_119, r.goal = 120 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_119 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 120)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 120) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 120 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 120 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_119 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_119 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_119 r hr, hg, hb, hp⟩

private def goalRecords_120 : List MiddleCertRecord := [
  ⟨121,0,[-1],359⟩,
  ⟨121,1,[-1],359⟩,
  ⟨121,2,[-1],359⟩,
  ⟨121,3,[-1],359⟩,
  ⟨121,4,[-1],359⟩,
  ⟨121,5,[-1],359⟩,
  ⟨121,6,[-1],359⟩,
  ⟨121,7,[-1],359⟩,
  ⟨121,8,[-1],396⟩,
  ⟨121,9,[-1],396⟩,
  ⟨121,10,[-1],396⟩,
  ⟨121,11,[-1],396⟩,
  ⟨121,12,[-1],396⟩,
  ⟨121,13,[-1],396⟩,
  ⟨121,14,[-1],396⟩,
  ⟨121,15,[-1],396⟩,
  ⟨121,16,[-1],356⟩,
  ⟨121,17,[-1],356⟩,
  ⟨121,18,[-1],356⟩,
  ⟨121,19,[-1],356⟩,
  ⟨121,20,[-1],361⟩,
  ⟨121,21,[-1],361⟩,
  ⟨121,22,[-1],361⟩,
  ⟨121,23,[-1],361⟩,
  ⟨121,24,[-1],356⟩,
  ⟨121,25,[-1],356⟩,
  ⟨121,26,[-1],356⟩,
  ⟨121,27,[-1],356⟩,
  ⟨121,28,[-1],385⟩,
  ⟨121,29,[-1],370⟩,
  ⟨121,30,[-1],375⟩,
  ⟨121,31,[-1],400⟩,
  ⟨121,32,[-1],359⟩,
  ⟨121,33,[-1],359⟩,
  ⟨121,34,[-1],359⟩,
  ⟨121,35,[-1],359⟩,
  ⟨121,36,[-1],359⟩,
  ⟨121,37,[-1],359⟩,
  ⟨121,38,[-1],359⟩,
  ⟨121,39,[-1],359⟩,
  ⟨121,40,[-1],396⟩,
  ⟨121,41,[-1],396⟩,
  ⟨121,42,[-1],396⟩,
  ⟨121,43,[-1],396⟩,
  ⟨121,44,[-1],396⟩,
  ⟨121,45,[-1],396⟩,
  ⟨121,46,[-1],396⟩,
  ⟨121,47,[-1],396⟩,
  ⟨121,48,[-1],356⟩,
  ⟨121,49,[-1],356⟩,
  ⟨121,50,[-1],356⟩,
  ⟨121,51,[-1],356⟩,
  ⟨121,52,[-1],361⟩,
  ⟨121,53,[-1],361⟩,
  ⟨121,54,[-1],361⟩,
  ⟨121,55,[-1],361⟩,
  ⟨121,56,[-1],356⟩,
  ⟨121,57,[-1],356⟩,
  ⟨121,58,[-1],356⟩,
  ⟨121,59,[-1],356⟩,
  ⟨121,60,[-1],385⟩,
  ⟨121,61,[-1],370⟩,
  ⟨121,62,[-1],375⟩,
  ⟨121,63,[-1],400⟩
]

private theorem goal_subset_120 : ∀ r ∈ goalRecords_120, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_120 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 121)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 121) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_120, r.goal = 121 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_120, r.goal = 121 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_120 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 121)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 121) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 121 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 121 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_120 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_120 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_120 r hr, hg, hb, hp⟩

private def goalRecords_121 : List MiddleCertRecord := [
  ⟨122,0,[-1],224⟩,
  ⟨122,1,[-1],224⟩,
  ⟨122,2,[-1],224⟩,
  ⟨122,3,[-1],224⟩,
  ⟨122,4,[-1],799⟩,
  ⟨122,5,[-1],799⟩,
  ⟨122,6,[-1],799⟩,
  ⟨122,7,[-1],799⟩,
  ⟨122,8,[-1],929⟩,
  ⟨122,9,[-1],1121⟩,
  ⟨122,10,[-1],1193⟩,
  ⟨122,11,[-1],669⟩,
  ⟨122,12,[-1],799⟩,
  ⟨122,13,[-1],799⟩,
  ⟨122,14,[-1],799⟩,
  ⟨122,15,[-1],799⟩,
  ⟨122,16,[-1],1175⟩,
  ⟨122,17,[-1],1175⟩,
  ⟨122,18,[-1],1175⟩,
  ⟨122,19,[-1],1175⟩,
  ⟨122,20,[-1],1175⟩,
  ⟨122,21,[-1],1175⟩,
  ⟨122,22,[-1],1175⟩,
  ⟨122,23,[-1],1175⟩,
  ⟨122,24,[-1],997⟩,
  ⟨122,25,[-1],997⟩,
  ⟨122,26,[-1],997⟩,
  ⟨122,27,[-1],997⟩,
  ⟨122,28,[-1],997⟩,
  ⟨122,29,[-1],997⟩,
  ⟨122,30,[-1],997⟩,
  ⟨122,31,[-1],997⟩,
  ⟨122,32,[-1],224⟩,
  ⟨122,33,[-1],224⟩,
  ⟨122,34,[-1],224⟩,
  ⟨122,35,[-1],224⟩,
  ⟨122,36,[-1],799⟩,
  ⟨122,37,[-1],799⟩,
  ⟨122,38,[-1],799⟩,
  ⟨122,39,[-1],799⟩,
  ⟨122,40,[-1],929⟩,
  ⟨122,41,[-1],1121⟩,
  ⟨122,42,[-1],1193⟩,
  ⟨122,43,[-1],669⟩,
  ⟨122,44,[-1],799⟩,
  ⟨122,45,[-1],799⟩,
  ⟨122,46,[-1],799⟩,
  ⟨122,47,[-1],799⟩,
  ⟨122,48,[-1],1175⟩,
  ⟨122,49,[-1],1175⟩,
  ⟨122,50,[-1],1175⟩,
  ⟨122,51,[-1],1175⟩,
  ⟨122,52,[-1],1175⟩,
  ⟨122,53,[-1],1175⟩,
  ⟨122,54,[-1],1175⟩,
  ⟨122,55,[-1],1175⟩,
  ⟨122,56,[-1],997⟩,
  ⟨122,57,[-1],997⟩,
  ⟨122,58,[-1],997⟩,
  ⟨122,59,[-1],997⟩,
  ⟨122,60,[-1],997⟩,
  ⟨122,61,[-1],997⟩,
  ⟨122,62,[-1],997⟩,
  ⟨122,63,[-1],997⟩
]

private theorem goal_subset_121 : ∀ r ∈ goalRecords_121, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_121 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 122)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 122) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_121, r.goal = 122 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_121, r.goal = 122 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_121 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 122)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 122) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 122 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 122 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_121 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_121 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_121 r hr, hg, hb, hp⟩

private def goalRecords_122 : List MiddleCertRecord := [

]

private theorem goal_subset_122 : ∀ r ∈ goalRecords_122, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_122 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 123)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 123) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_122, r.goal = 123 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_122, r.goal = 123 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_122 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 123)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 123) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 123 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 123 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_122 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_122 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_122 r hr, hg, hb, hp⟩

private def goalRecords_123 : List MiddleCertRecord := [
  ⟨124,0,[-1],348⟩,
  ⟨124,1,[-1],397⟩,
  ⟨124,2,[-1],362⟩,
  ⟨124,3,[-1],402⟩,
  ⟨124,4,[-1],348⟩,
  ⟨124,5,[-1],397⟩,
  ⟨124,6,[-1],373⟩,
  ⟨124,7,[-1],368⟩,
  ⟨124,8,[-1],348⟩,
  ⟨124,9,[-1],397⟩,
  ⟨124,10,[-1],362⟩,
  ⟨124,11,[-1],367⟩,
  ⟨124,12,[-1],348⟩,
  ⟨124,13,[-1],397⟩,
  ⟨124,14,[-1],362⟩,
  ⟨124,15,[-1],392⟩
]

private theorem goal_subset_123 : ∀ r ∈ goalRecords_123, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_123 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 124)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 124) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_123, r.goal = 124 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_123, r.goal = 124 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_123 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 124)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 124) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 124 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 124 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_123 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_123 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_123 r hr, hg, hb, hp⟩

private def goalRecords_124 : List MiddleCertRecord := [
  ⟨125,0,[-1],414⟩,
  ⟨125,1,[-1],380⟩,
  ⟨125,2,[-1],468⟩,
  ⟨125,3,[-1],468⟩,
  ⟨125,4,[-1],414⟩,
  ⟨125,5,[-1],380⟩,
  ⟨125,6,[-1],905⟩,
  ⟨125,7,[-1],614⟩,
  ⟨125,8,[-1],716⟩,
  ⟨125,9,[-1],720⟩,
  ⟨125,10,[-1],719⟩,
  ⟨125,11,[-1],719⟩,
  ⟨125,12,[-1],1163⟩,
  ⟨125,13,[-1],1165⟩,
  ⟨125,14,[-1],1164⟩,
  ⟨125,15,[-1],1164⟩
]

private theorem goal_subset_124 : ∀ r ∈ goalRecords_124, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_124 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 125)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 125) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_124, r.goal = 125 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_124, r.goal = 125 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_124 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 125)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 125) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 125 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 125 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_124 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_124 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_124 r hr, hg, hb, hp⟩

private def goalRecords_125 : List MiddleCertRecord := [

]

private theorem goal_subset_125 : ∀ r ∈ goalRecords_125, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_125 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 126)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 126) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_125, r.goal = 126 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_125, r.goal = 126 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_125 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 126)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 126) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 126 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 126 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_125 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_125 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_125 r hr, hg, hb, hp⟩

private def goalRecords_126 : List MiddleCertRecord := [
  ⟨127,0,[-1],345⟩,
  ⟨127,1,[-1],403⟩,
  ⟨127,2,[-1],350⟩,
  ⟨127,3,[-1],404⟩,
  ⟨127,4,[-1],345⟩,
  ⟨127,5,[-1],403⟩,
  ⟨127,6,[-1],364⟩,
  ⟨127,7,[-1],377⟩,
  ⟨127,8,[-1],345⟩,
  ⟨127,9,[-1],403⟩,
  ⟨127,10,[-1],350⟩,
  ⟨127,11,[-1],363⟩,
  ⟨127,12,[-1],345⟩,
  ⟨127,13,[-1],403⟩,
  ⟨127,14,[-1],350⟩,
  ⟨127,15,[-1],393⟩
]

private theorem goal_subset_126 : ∀ r ∈ goalRecords_126, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_126 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 127)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 127) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_126, r.goal = 127 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_126, r.goal = 127 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_126 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 127)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 127) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 127 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 127 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_126 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_126 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_126 r hr, hg, hb, hp⟩

private def goalRecords_127 : List MiddleCertRecord := [
  ⟨128,0,[-1],8⟩,
  ⟨128,1,[-1],8⟩,
  ⟨128,2,[-1],8⟩,
  ⟨128,3,[-1],8⟩,
  ⟨128,4,[-1],592⟩,
  ⟨128,5,[-1],705⟩,
  ⟨128,6,[-1],599⟩,
  ⟨128,7,[-1],1002⟩,
  ⟨128,8,[-1],763⟩,
  ⟨128,9,[-1],763⟩,
  ⟨128,10,[-1],763⟩,
  ⟨128,11,[-1],763⟩,
  ⟨128,12,[-1],687⟩,
  ⟨128,13,[-1],687⟩,
  ⟨128,14,[-1],687⟩,
  ⟨128,15,[-1],687⟩
]

private theorem goal_subset_127 : ∀ r ∈ goalRecords_127, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_127 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 128)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 128) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_127, r.goal = 128 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_127, r.goal = 128 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_127 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 128)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 128) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 128 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 128 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_127 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_127 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_127 r hr, hg, hb, hp⟩

private def goalRecords_128 : List MiddleCertRecord := [
  ⟨129,0,[-1],344⟩,
  ⟨129,1,[-1],387⟩,
  ⟨129,2,[-1],360⟩,
  ⟨129,3,[-1],346⟩,
  ⟨129,4,[-1],344⟩,
  ⟨129,5,[-1],387⟩,
  ⟨129,6,[-1],360⟩,
  ⟨129,7,[-1],391⟩,
  ⟨129,8,[-1],344⟩,
  ⟨129,9,[-1],387⟩,
  ⟨129,10,[-1],360⟩,
  ⟨129,11,[-1],346⟩,
  ⟨129,12,[-1],344⟩,
  ⟨129,13,[-1],387⟩,
  ⟨129,14,[-1],360⟩,
  ⟨129,15,[-1],366⟩,
  ⟨129,16,[-1],344⟩,
  ⟨129,17,[-1],387⟩,
  ⟨129,18,[-1],360⟩,
  ⟨129,19,[-1],346⟩,
  ⟨129,20,[-1],344⟩,
  ⟨129,21,[-1],387⟩,
  ⟨129,22,[-1],360⟩,
  ⟨129,23,[-1],371⟩,
  ⟨129,24,[-1],344⟩,
  ⟨129,25,[-1],387⟩,
  ⟨129,26,[-1],360⟩,
  ⟨129,27,[-1],346⟩,
  ⟨129,28,[-1],344⟩,
  ⟨129,29,[-1],387⟩,
  ⟨129,30,[-1],360⟩,
  ⟨129,31,[-1],394⟩
]

private theorem goal_subset_128 : ∀ r ∈ goalRecords_128, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_128 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 129)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 129) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_128, r.goal = 129 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_128, r.goal = 129 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_128 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 129)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 129) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 129 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 129 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_128 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_128 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_128 r hr, hg, hb, hp⟩

private def goalRecords_129 : List MiddleCertRecord := [

]

private theorem goal_subset_129 : ∀ r ∈ goalRecords_129, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_129 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 130)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 130) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_129, r.goal = 130 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_129, r.goal = 130 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_129 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 130)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 130) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 130 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 130 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_129 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_129 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_129 r hr, hg, hb, hp⟩

private def goalRecords_130 : List MiddleCertRecord := [
  ⟨131,0,[-1],347⟩,
  ⟨131,1,[-1],389⟩,
  ⟨131,2,[-1],346⟩,
  ⟨131,3,[-1],346⟩,
  ⟨131,4,[-1],347⟩,
  ⟨131,5,[-1],389⟩,
  ⟨131,6,[-1],346⟩,
  ⟨131,7,[-1],346⟩,
  ⟨131,8,[-1],347⟩,
  ⟨131,9,[-1],389⟩,
  ⟨131,10,[-1],346⟩,
  ⟨131,11,[-1],346⟩,
  ⟨131,12,[-1],347⟩,
  ⟨131,13,[-1],389⟩,
  ⟨131,14,[-1],346⟩,
  ⟨131,15,[-1],346⟩,
  ⟨131,16,[-1],347⟩,
  ⟨131,17,[-1],389⟩,
  ⟨131,18,[-1],346⟩,
  ⟨131,19,[-1],346⟩,
  ⟨131,20,[-1],347⟩,
  ⟨131,21,[-1],389⟩,
  ⟨131,22,[-1],346⟩,
  ⟨131,23,[-1],346⟩,
  ⟨131,24,[-1],347⟩,
  ⟨131,25,[-1],389⟩,
  ⟨131,26,[-1],346⟩,
  ⟨131,27,[-1],346⟩,
  ⟨131,28,[-1],347⟩,
  ⟨131,29,[-1],389⟩,
  ⟨131,30,[-1],346⟩,
  ⟨131,31,[-1],346⟩,
  ⟨131,32,[-1],347⟩,
  ⟨131,33,[-1],389⟩,
  ⟨131,34,[-1],354⟩,
  ⟨131,35,[-1],398⟩,
  ⟨131,36,[-1],347⟩,
  ⟨131,37,[-1],389⟩,
  ⟨131,38,[-1],354⟩,
  ⟨131,39,[-1],398⟩,
  ⟨131,40,[-1],347⟩,
  ⟨131,41,[-1],389⟩,
  ⟨131,42,[-1],354⟩,
  ⟨131,43,[-1],374⟩,
  ⟨131,44,[-1],347⟩,
  ⟨131,45,[-1],389⟩,
  ⟨131,46,[-1],354⟩,
  ⟨131,47,[-1],374⟩,
  ⟨131,48,[-1],347⟩,
  ⟨131,49,[-1],389⟩,
  ⟨131,50,[-1],354⟩,
  ⟨131,51,[-1],378⟩,
  ⟨131,52,[-1],347⟩,
  ⟨131,53,[-1],389⟩,
  ⟨131,54,[-1],354⟩,
  ⟨131,55,[-1],378⟩,
  ⟨131,56,[-1],347⟩,
  ⟨131,57,[-1],389⟩,
  ⟨131,58,[-1],354⟩,
  ⟨131,59,[-1],382⟩,
  ⟨131,60,[-1],347⟩,
  ⟨131,61,[-1],389⟩,
  ⟨131,62,[-1],354⟩,
  ⟨131,63,[-1],382⟩
]

private theorem goal_subset_130 : ∀ r ∈ goalRecords_130, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_130 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 131)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 131) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_130, r.goal = 131 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_130, r.goal = 131 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_130 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 131)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 131) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 131 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 131 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_130 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_130 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_130 r hr, hg, hb, hp⟩

private def goalRecords_131 : List MiddleCertRecord := [

]

private theorem goal_subset_131 : ∀ r ∈ goalRecords_131, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_131 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 132)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 132) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_131, r.goal = 132 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ goalRecords_131, r.goal = 132 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_131 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 132)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 132) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 132 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = 132 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_131 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_131 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_131 r hr, hg, hb, hp⟩

private theorem coverage :
    ∀ i ∈ selectedGoals,
      ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData (i+1))).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData (i+1)) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (7 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 7)).length,
          ∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents)  := by
  simp only [selectedGoals, List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨cover_117, cover_118, cover_119, cover_120, cover_121, cover_122, cover_123, cover_124, cover_125, cover_126, cover_127, cover_128, cover_129, cover_130, cover_131, List.forall_mem_nil _⟩

end FastFamily7

open FastFamily7

theorem solution : middleCertFamilyValid middleCertData 7 := by
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
