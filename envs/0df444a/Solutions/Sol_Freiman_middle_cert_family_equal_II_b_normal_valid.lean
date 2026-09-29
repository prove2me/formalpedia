-- Prove2me | solution 1 for Freiman.middle_cert_family_equal_II_b_normal_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:05:53.527991+00:00
-- url     : https://prove2.me/submissions/8af6fbef-7cc1-4d89-8269-b7007188cced

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

namespace FastFamily6

private def selectedRecords : List MiddleCertRecord := [
  ⟨98,4,[-1],406⟩,
  ⟨98,6,[-1],734⟩,
  ⟨98,7,[-1],1135⟩,
  ⟨98,12,[-1],739⟩,
  ⟨98,13,[-1],739⟩,
  ⟨98,14,[-1],739⟩,
  ⟨99,1,[-1],407⟩,
  ⟨99,2,[-1],739⟩,
  ⟨99,3,[-1],739⟩,
  ⟨99,7,[-1],739⟩,
  ⟨99,8,[-1],745⟩,
  ⟨99,9,[-1],745⟩,
  ⟨99,11,[-1],1137⟩,
  ⟨99,13,[-1],1138⟩,
  ⟨99,17,[-1],407⟩,
  ⟨99,18,[-1],739⟩,
  ⟨99,19,[-1],739⟩,
  ⟨99,23,[-1],739⟩,
  ⟨99,24,[-1],744⟩,
  ⟨99,25,[-1],744⟩,
  ⟨99,27,[-1],1137⟩,
  ⟨99,29,[-1],1136⟩,
  ⟨101,0,[-1],247⟩,
  ⟨101,1,[-1],247⟩,
  ⟨101,2,[-1],1050⟩,
  ⟨101,3,[-1],993⟩,
  ⟨101,4,[-1],247⟩,
  ⟨101,5,[-1],247⟩,
  ⟨101,6,[-1],1050⟩,
  ⟨101,7,[-1],993⟩,
  ⟨101,8,[-1],259⟩,
  ⟨101,9,[-1],259⟩,
  ⟨101,10,[-1],1052⟩,
  ⟨101,11,[-1],994⟩,
  ⟨101,12,[-1],259⟩,
  ⟨101,13,[-1],259⟩,
  ⟨101,14,[-1],1052⟩,
  ⟨101,15,[-1],994⟩,
  ⟨101,16,[-1],239⟩,
  ⟨101,17,[-1],239⟩,
  ⟨101,18,[-1],1048⟩,
  ⟨101,19,[-1],991⟩,
  ⟨101,20,[-1],240⟩,
  ⟨101,21,[-1],240⟩,
  ⟨101,22,[-1],1049⟩,
  ⟨101,23,[-1],992⟩,
  ⟨101,24,[-1],239⟩,
  ⟨101,25,[-1],239⟩,
  ⟨101,26,[-1],1048⟩,
  ⟨101,27,[-1],991⟩,
  ⟨101,28,[-1],265⟩,
  ⟨101,29,[-1],258⟩,
  ⟨101,30,[-1],1051⟩,
  ⟨101,31,[-1],995⟩,
  ⟨101,32,[-1],1090⟩,
  ⟨101,33,[-1],1090⟩,
  ⟨101,34,[-1],1090⟩,
  ⟨101,35,[-1],993⟩,
  ⟨101,36,[-1],1090⟩,
  ⟨101,37,[-1],1090⟩,
  ⟨101,38,[-1],1090⟩,
  ⟨101,39,[-1],993⟩,
  ⟨101,40,[-1],1093⟩,
  ⟨101,41,[-1],1093⟩,
  ⟨101,42,[-1],1093⟩,
  ⟨101,43,[-1],994⟩,
  ⟨101,44,[-1],1093⟩,
  ⟨101,45,[-1],1093⟩,
  ⟨101,46,[-1],1093⟩,
  ⟨101,47,[-1],994⟩,
  ⟨101,48,[-1],1088⟩,
  ⟨101,49,[-1],1088⟩,
  ⟨101,50,[-1],1088⟩,
  ⟨101,51,[-1],991⟩,
  ⟨101,52,[-1],1089⟩,
  ⟨101,53,[-1],1089⟩,
  ⟨101,54,[-1],1089⟩,
  ⟨101,55,[-1],992⟩,
  ⟨101,56,[-1],1088⟩,
  ⟨101,57,[-1],1088⟩,
  ⟨101,58,[-1],1088⟩,
  ⟨101,59,[-1],991⟩,
  ⟨101,60,[-1],1094⟩,
  ⟨101,61,[-1],1092⟩,
  ⟨101,62,[-1],1091⟩,
  ⟨101,63,[-1],995⟩,
  ⟨102,0,[-1],490⟩,
  ⟨102,1,[-1],490⟩,
  ⟨102,2,[-1],490⟩,
  ⟨102,3,[-1],490⟩,
  ⟨102,4,[-1],802⟩,
  ⟨102,5,[-1],802⟩,
  ⟨102,6,[-1],802⟩,
  ⟨102,7,[-1],802⟩,
  ⟨102,8,[-1],825⟩,
  ⟨102,9,[-1],797⟩,
  ⟨102,10,[-1],817⟩,
  ⟨102,11,[-1],663⟩,
  ⟨102,12,[-1],802⟩,
  ⟨102,13,[-1],802⟩,
  ⟨102,14,[-1],802⟩,
  ⟨102,15,[-1],802⟩,
  ⟨102,16,[-1],925⟩,
  ⟨102,17,[-1],925⟩,
  ⟨102,18,[-1],925⟩,
  ⟨102,19,[-1],925⟩,
  ⟨102,20,[-1],925⟩,
  ⟨102,21,[-1],925⟩,
  ⟨102,22,[-1],925⟩,
  ⟨102,23,[-1],925⟩,
  ⟨102,24,[-1],1168⟩,
  ⟨102,25,[-1],1168⟩,
  ⟨102,26,[-1],1168⟩,
  ⟨102,27,[-1],1168⟩,
  ⟨102,28,[-1],1168⟩,
  ⟨102,29,[-1],1168⟩,
  ⟨102,30,[-1],1168⟩,
  ⟨102,31,[-1],1168⟩,
  ⟨102,32,[-1],490⟩,
  ⟨102,33,[-1],490⟩,
  ⟨102,34,[-1],490⟩,
  ⟨102,35,[-1],490⟩,
  ⟨102,36,[-1],802⟩,
  ⟨102,37,[-1],802⟩,
  ⟨102,38,[-1],802⟩,
  ⟨102,39,[-1],802⟩,
  ⟨102,40,[-1],825⟩,
  ⟨102,41,[-1],797⟩,
  ⟨102,42,[-1],817⟩,
  ⟨102,43,[-1],663⟩,
  ⟨102,44,[-1],802⟩,
  ⟨102,45,[-1],802⟩,
  ⟨102,46,[-1],802⟩,
  ⟨102,47,[-1],802⟩,
  ⟨102,48,[-1],925⟩,
  ⟨102,49,[-1],925⟩,
  ⟨102,50,[-1],925⟩,
  ⟨102,51,[-1],925⟩,
  ⟨102,52,[-1],925⟩,
  ⟨102,53,[-1],925⟩,
  ⟨102,54,[-1],925⟩,
  ⟨102,55,[-1],925⟩,
  ⟨102,56,[-1],1168⟩,
  ⟨102,57,[-1],1168⟩,
  ⟨102,58,[-1],1168⟩,
  ⟨102,59,[-1],1168⟩,
  ⟨102,60,[-1],1168⟩,
  ⟨102,61,[-1],1168⟩,
  ⟨102,62,[-1],1168⟩,
  ⟨102,63,[-1],1168⟩,
  ⟨104,0,[-1],243⟩,
  ⟨104,1,[-1],243⟩,
  ⟨104,2,[-1],243⟩,
  ⟨104,3,[-1],243⟩,
  ⟨104,4,[-1],243⟩,
  ⟨104,5,[-1],243⟩,
  ⟨104,6,[-1],243⟩,
  ⟨104,7,[-1],243⟩,
  ⟨104,8,[-1],266⟩,
  ⟨104,9,[-1],266⟩,
  ⟨104,10,[-1],266⟩,
  ⟨104,11,[-1],266⟩,
  ⟨104,12,[-1],266⟩,
  ⟨104,13,[-1],266⟩,
  ⟨104,14,[-1],266⟩,
  ⟨104,15,[-1],266⟩,
  ⟨104,16,[-1],242⟩,
  ⟨104,17,[-1],242⟩,
  ⟨104,18,[-1],242⟩,
  ⟨104,19,[-1],242⟩,
  ⟨104,20,[-1],245⟩,
  ⟨104,21,[-1],245⟩,
  ⟨104,22,[-1],245⟩,
  ⟨104,23,[-1],245⟩,
  ⟨104,24,[-1],242⟩,
  ⟨104,25,[-1],242⟩,
  ⟨104,26,[-1],242⟩,
  ⟨104,27,[-1],242⟩,
  ⟨104,28,[-1],260⟩,
  ⟨104,29,[-1],253⟩,
  ⟨104,30,[-1],256⟩,
  ⟨104,31,[-1],269⟩,
  ⟨104,32,[-1],243⟩,
  ⟨104,33,[-1],243⟩,
  ⟨104,34,[-1],243⟩,
  ⟨104,35,[-1],243⟩,
  ⟨104,36,[-1],243⟩,
  ⟨104,37,[-1],243⟩,
  ⟨104,38,[-1],243⟩,
  ⟨104,39,[-1],243⟩,
  ⟨104,40,[-1],266⟩,
  ⟨104,41,[-1],266⟩,
  ⟨104,42,[-1],266⟩,
  ⟨104,43,[-1],266⟩,
  ⟨104,44,[-1],266⟩,
  ⟨104,45,[-1],266⟩,
  ⟨104,46,[-1],266⟩,
  ⟨104,47,[-1],266⟩,
  ⟨104,48,[-1],242⟩,
  ⟨104,49,[-1],242⟩,
  ⟨104,50,[-1],242⟩,
  ⟨104,51,[-1],242⟩,
  ⟨104,52,[-1],245⟩,
  ⟨104,53,[-1],245⟩,
  ⟨104,54,[-1],245⟩,
  ⟨104,55,[-1],245⟩,
  ⟨104,56,[-1],242⟩,
  ⟨104,57,[-1],242⟩,
  ⟨104,58,[-1],242⟩,
  ⟨104,59,[-1],242⟩,
  ⟨104,60,[-1],260⟩,
  ⟨104,61,[-1],253⟩,
  ⟨104,62,[-1],256⟩,
  ⟨104,63,[-1],269⟩,
  ⟨105,0,[-1],224⟩,
  ⟨105,1,[-1],224⟩,
  ⟨105,2,[-1],224⟩,
  ⟨105,3,[-1],224⟩,
  ⟨105,4,[-1],799⟩,
  ⟨105,5,[-1],799⟩,
  ⟨105,6,[-1],799⟩,
  ⟨105,7,[-1],799⟩,
  ⟨105,8,[-1],929⟩,
  ⟨105,9,[-1],1121⟩,
  ⟨105,10,[-1],1193⟩,
  ⟨105,11,[-1],669⟩,
  ⟨105,12,[-1],799⟩,
  ⟨105,13,[-1],799⟩,
  ⟨105,14,[-1],799⟩,
  ⟨105,15,[-1],799⟩,
  ⟨105,16,[-1],1175⟩,
  ⟨105,17,[-1],1175⟩,
  ⟨105,18,[-1],1175⟩,
  ⟨105,19,[-1],1175⟩,
  ⟨105,20,[-1],1175⟩,
  ⟨105,21,[-1],1175⟩,
  ⟨105,22,[-1],1175⟩,
  ⟨105,23,[-1],1175⟩,
  ⟨105,24,[-1],997⟩,
  ⟨105,25,[-1],997⟩,
  ⟨105,26,[-1],997⟩,
  ⟨105,27,[-1],997⟩,
  ⟨105,28,[-1],997⟩,
  ⟨105,29,[-1],997⟩,
  ⟨105,30,[-1],997⟩,
  ⟨105,31,[-1],997⟩,
  ⟨105,32,[-1],224⟩,
  ⟨105,33,[-1],224⟩,
  ⟨105,34,[-1],224⟩,
  ⟨105,35,[-1],224⟩,
  ⟨105,36,[-1],799⟩,
  ⟨105,37,[-1],799⟩,
  ⟨105,38,[-1],799⟩,
  ⟨105,39,[-1],799⟩,
  ⟨105,40,[-1],929⟩,
  ⟨105,41,[-1],1121⟩,
  ⟨105,42,[-1],1193⟩,
  ⟨105,43,[-1],669⟩,
  ⟨105,44,[-1],799⟩,
  ⟨105,45,[-1],799⟩,
  ⟨105,46,[-1],799⟩,
  ⟨105,47,[-1],799⟩,
  ⟨105,48,[-1],1175⟩,
  ⟨105,49,[-1],1175⟩,
  ⟨105,50,[-1],1175⟩,
  ⟨105,51,[-1],1175⟩,
  ⟨105,52,[-1],1175⟩,
  ⟨105,53,[-1],1175⟩,
  ⟨105,54,[-1],1175⟩,
  ⟨105,55,[-1],1175⟩,
  ⟨105,56,[-1],997⟩,
  ⟨105,57,[-1],997⟩,
  ⟨105,58,[-1],997⟩,
  ⟨105,59,[-1],997⟩,
  ⟨105,60,[-1],997⟩,
  ⟨105,61,[-1],997⟩,
  ⟨105,62,[-1],997⟩,
  ⟨105,63,[-1],997⟩,
  ⟨107,0,[-1],237⟩,
  ⟨107,1,[-1],267⟩,
  ⟨107,2,[-1],246⟩,
  ⟨107,3,[-1],270⟩,
  ⟨107,4,[-1],237⟩,
  ⟨107,5,[-1],267⟩,
  ⟨107,6,[-1],254⟩,
  ⟨107,7,[-1],252⟩,
  ⟨107,8,[-1],237⟩,
  ⟨107,9,[-1],267⟩,
  ⟨107,10,[-1],246⟩,
  ⟨107,11,[-1],251⟩,
  ⟨107,12,[-1],237⟩,
  ⟨107,13,[-1],267⟩,
  ⟨107,14,[-1],246⟩,
  ⟨107,15,[-1],263⟩,
  ⟨108,0,[-1],467⟩,
  ⟨108,1,[-1],469⟩,
  ⟨108,2,[-1],468⟩,
  ⟨108,3,[-1],468⟩,
  ⟨108,4,[-1],1082⟩,
  ⟨108,5,[-1],1032⟩,
  ⟨108,6,[-1],905⟩,
  ⟨108,7,[-1],614⟩,
  ⟨108,8,[-1],716⟩,
  ⟨108,9,[-1],720⟩,
  ⟨108,10,[-1],719⟩,
  ⟨108,11,[-1],719⟩,
  ⟨108,12,[-1],1163⟩,
  ⟨108,13,[-1],1165⟩,
  ⟨108,14,[-1],1164⟩,
  ⟨108,15,[-1],1164⟩,
  ⟨110,0,[-1],234⟩,
  ⟨110,1,[-1],271⟩,
  ⟨110,2,[-1],238⟩,
  ⟨110,3,[-1],272⟩,
  ⟨110,4,[-1],234⟩,
  ⟨110,5,[-1],271⟩,
  ⟨110,6,[-1],249⟩,
  ⟨110,7,[-1],257⟩,
  ⟨110,8,[-1],234⟩,
  ⟨110,9,[-1],271⟩,
  ⟨110,10,[-1],238⟩,
  ⟨110,11,[-1],248⟩,
  ⟨110,12,[-1],234⟩,
  ⟨110,13,[-1],271⟩,
  ⟨110,14,[-1],238⟩,
  ⟨110,15,[-1],264⟩,
  ⟨111,0,[-1],8⟩,
  ⟨111,1,[-1],8⟩,
  ⟨111,2,[-1],8⟩,
  ⟨111,3,[-1],8⟩,
  ⟨111,4,[-1],592⟩,
  ⟨111,5,[-1],705⟩,
  ⟨111,6,[-1],599⟩,
  ⟨111,7,[-1],1002⟩,
  ⟨111,8,[-1],763⟩,
  ⟨111,9,[-1],763⟩,
  ⟨111,10,[-1],763⟩,
  ⟨111,11,[-1],763⟩,
  ⟨111,12,[-1],687⟩,
  ⟨111,13,[-1],687⟩,
  ⟨111,14,[-1],687⟩,
  ⟨111,15,[-1],687⟩,
  ⟨112,0,[-1],449⟩,
  ⟨112,1,[-1],449⟩,
  ⟨112,2,[-1],449⟩,
  ⟨112,3,[-1],449⟩,
  ⟨112,4,[-1],605⟩,
  ⟨112,5,[-1],827⟩,
  ⟨112,6,[-1],924⟩,
  ⟨112,7,[-1],926⟩,
  ⟨112,8,[-1],733⟩,
  ⟨112,9,[-1],736⟩,
  ⟨112,10,[-1],734⟩,
  ⟨112,11,[-1],734⟩,
  ⟨112,12,[-1],1151⟩,
  ⟨112,13,[-1],1152⟩,
  ⟨112,14,[-1],1151⟩,
  ⟨112,15,[-1],1151⟩,
  ⟨114,0,[-1],335⟩,
  ⟨114,1,[-1],340⟩,
  ⟨114,2,[-1],338⟩,
  ⟨114,3,[-1],336⟩,
  ⟨114,4,[-1],335⟩,
  ⟨114,5,[-1],340⟩,
  ⟨114,6,[-1],338⟩,
  ⟨114,7,[-1],342⟩,
  ⟨114,8,[-1],233⟩,
  ⟨114,9,[-1],261⟩,
  ⟨114,10,[-1],244⟩,
  ⟨114,11,[-1],235⟩,
  ⟨114,12,[-1],233⟩,
  ⟨114,13,[-1],261⟩,
  ⟨114,14,[-1],244⟩,
  ⟨114,15,[-1],250⟩,
  ⟨114,16,[-1],834⟩,
  ⟨114,17,[-1],845⟩,
  ⟨114,18,[-1],839⟩,
  ⟨114,19,[-1],835⟩,
  ⟨114,20,[-1],834⟩,
  ⟨114,21,[-1],845⟩,
  ⟨114,22,[-1],839⟩,
  ⟨114,23,[-1],841⟩,
  ⟨114,24,[-1],1106⟩,
  ⟨114,25,[-1],1111⟩,
  ⟨114,26,[-1],1109⟩,
  ⟨114,27,[-1],1107⟩,
  ⟨114,28,[-1],1106⟩,
  ⟨114,29,[-1],1111⟩,
  ⟨114,30,[-1],1109⟩,
  ⟨114,31,[-1],1113⟩,
  ⟨116,0,[-1],236⟩,
  ⟨116,1,[-1],262⟩,
  ⟨116,2,[-1],235⟩,
  ⟨116,3,[-1],235⟩,
  ⟨116,4,[-1],236⟩,
  ⟨116,5,[-1],262⟩,
  ⟨116,6,[-1],235⟩,
  ⟨116,7,[-1],235⟩,
  ⟨116,8,[-1],236⟩,
  ⟨116,9,[-1],262⟩,
  ⟨116,10,[-1],235⟩,
  ⟨116,11,[-1],235⟩,
  ⟨116,12,[-1],236⟩,
  ⟨116,13,[-1],262⟩,
  ⟨116,14,[-1],235⟩,
  ⟨116,15,[-1],235⟩,
  ⟨116,16,[-1],543⟩,
  ⟨116,17,[-1],561⟩,
  ⟨116,18,[-1],542⟩,
  ⟨116,19,[-1],542⟩,
  ⟨116,20,[-1],543⟩,
  ⟨116,21,[-1],561⟩,
  ⟨116,22,[-1],542⟩,
  ⟨116,23,[-1],542⟩,
  ⟨116,24,[-1],956⟩,
  ⟨116,25,[-1],974⟩,
  ⟨116,26,[-1],955⟩,
  ⟨116,27,[-1],955⟩,
  ⟨116,28,[-1],956⟩,
  ⟨116,29,[-1],974⟩,
  ⟨116,30,[-1],955⟩,
  ⟨116,31,[-1],955⟩,
  ⟨116,32,[-1],236⟩,
  ⟨116,33,[-1],262⟩,
  ⟨116,34,[-1],241⟩,
  ⟨116,35,[-1],268⟩,
  ⟨116,36,[-1],236⟩,
  ⟨116,37,[-1],262⟩,
  ⟨116,38,[-1],241⟩,
  ⟨116,39,[-1],268⟩,
  ⟨116,40,[-1],236⟩,
  ⟨116,41,[-1],262⟩,
  ⟨116,42,[-1],241⟩,
  ⟨116,43,[-1],255⟩,
  ⟨116,44,[-1],236⟩,
  ⟨116,45,[-1],262⟩,
  ⟨116,46,[-1],241⟩,
  ⟨116,47,[-1],255⟩,
  ⟨116,48,[-1],543⟩,
  ⟨116,49,[-1],561⟩,
  ⟨116,50,[-1],547⟩,
  ⟨116,51,[-1],557⟩,
  ⟨116,52,[-1],543⟩,
  ⟨116,53,[-1],561⟩,
  ⟨116,54,[-1],547⟩,
  ⟨116,55,[-1],557⟩,
  ⟨116,56,[-1],956⟩,
  ⟨116,57,[-1],974⟩,
  ⟨116,58,[-1],960⟩,
  ⟨116,59,[-1],971⟩,
  ⟨116,60,[-1],956⟩,
  ⟨116,61,[-1],974⟩,
  ⟨116,62,[-1],960⟩,
  ⟨116,63,[-1],971⟩
]

private def selectedGoals : List ℕ := [97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]

private theorem records_eq :
    middleCertData.records.filter (fun r => decide ((middleCertGoal middleCertData r.goal).family = 6)) = selectedRecords := by
  decide +kernel

private theorem goals_eq :
    (List.range middleCertData.goals.length).filter (fun i => decide ((middleCertGoal middleCertData (i+1)).family = 6)) = selectedGoals := by
  decide +kernel

private def chunk_0 : List MiddleCertRecord := [
  ⟨98,4,[-1],406⟩,
  ⟨98,6,[-1],734⟩,
  ⟨98,7,[-1],1135⟩,
  ⟨98,12,[-1],739⟩,
  ⟨98,13,[-1],739⟩,
  ⟨98,14,[-1],739⟩,
  ⟨99,1,[-1],407⟩,
  ⟨99,2,[-1],739⟩,
  ⟨99,3,[-1],739⟩,
  ⟨99,7,[-1],739⟩,
  ⟨99,8,[-1],745⟩,
  ⟨99,9,[-1],745⟩,
  ⟨99,11,[-1],1137⟩,
  ⟨99,13,[-1],1138⟩,
  ⟨99,17,[-1],407⟩,
  ⟨99,18,[-1],739⟩
]

private theorem chunk_valid_0 : ∀ r ∈ chunk_0, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_1 : List MiddleCertRecord := [
  ⟨99,19,[-1],739⟩,
  ⟨99,23,[-1],739⟩,
  ⟨99,24,[-1],744⟩,
  ⟨99,25,[-1],744⟩,
  ⟨99,27,[-1],1137⟩,
  ⟨99,29,[-1],1136⟩,
  ⟨101,0,[-1],247⟩,
  ⟨101,1,[-1],247⟩,
  ⟨101,2,[-1],1050⟩,
  ⟨101,3,[-1],993⟩,
  ⟨101,4,[-1],247⟩,
  ⟨101,5,[-1],247⟩,
  ⟨101,6,[-1],1050⟩,
  ⟨101,7,[-1],993⟩,
  ⟨101,8,[-1],259⟩,
  ⟨101,9,[-1],259⟩
]

private theorem chunk_valid_1 : ∀ r ∈ chunk_1, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_2 : List MiddleCertRecord := [
  ⟨101,10,[-1],1052⟩,
  ⟨101,11,[-1],994⟩,
  ⟨101,12,[-1],259⟩,
  ⟨101,13,[-1],259⟩,
  ⟨101,14,[-1],1052⟩,
  ⟨101,15,[-1],994⟩,
  ⟨101,16,[-1],239⟩,
  ⟨101,17,[-1],239⟩,
  ⟨101,18,[-1],1048⟩,
  ⟨101,19,[-1],991⟩,
  ⟨101,20,[-1],240⟩,
  ⟨101,21,[-1],240⟩,
  ⟨101,22,[-1],1049⟩,
  ⟨101,23,[-1],992⟩,
  ⟨101,24,[-1],239⟩,
  ⟨101,25,[-1],239⟩
]

private theorem chunk_valid_2 : ∀ r ∈ chunk_2, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_3 : List MiddleCertRecord := [
  ⟨101,26,[-1],1048⟩,
  ⟨101,27,[-1],991⟩,
  ⟨101,28,[-1],265⟩,
  ⟨101,29,[-1],258⟩,
  ⟨101,30,[-1],1051⟩,
  ⟨101,31,[-1],995⟩,
  ⟨101,32,[-1],1090⟩,
  ⟨101,33,[-1],1090⟩,
  ⟨101,34,[-1],1090⟩,
  ⟨101,35,[-1],993⟩,
  ⟨101,36,[-1],1090⟩,
  ⟨101,37,[-1],1090⟩,
  ⟨101,38,[-1],1090⟩,
  ⟨101,39,[-1],993⟩,
  ⟨101,40,[-1],1093⟩,
  ⟨101,41,[-1],1093⟩
]

private theorem chunk_valid_3 : ∀ r ∈ chunk_3, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_4 : List MiddleCertRecord := [
  ⟨101,42,[-1],1093⟩,
  ⟨101,43,[-1],994⟩,
  ⟨101,44,[-1],1093⟩,
  ⟨101,45,[-1],1093⟩,
  ⟨101,46,[-1],1093⟩,
  ⟨101,47,[-1],994⟩,
  ⟨101,48,[-1],1088⟩,
  ⟨101,49,[-1],1088⟩,
  ⟨101,50,[-1],1088⟩,
  ⟨101,51,[-1],991⟩,
  ⟨101,52,[-1],1089⟩,
  ⟨101,53,[-1],1089⟩,
  ⟨101,54,[-1],1089⟩,
  ⟨101,55,[-1],992⟩,
  ⟨101,56,[-1],1088⟩,
  ⟨101,57,[-1],1088⟩
]

private theorem chunk_valid_4 : ∀ r ∈ chunk_4, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_5 : List MiddleCertRecord := [
  ⟨101,58,[-1],1088⟩,
  ⟨101,59,[-1],991⟩,
  ⟨101,60,[-1],1094⟩,
  ⟨101,61,[-1],1092⟩,
  ⟨101,62,[-1],1091⟩,
  ⟨101,63,[-1],995⟩,
  ⟨102,0,[-1],490⟩,
  ⟨102,1,[-1],490⟩,
  ⟨102,2,[-1],490⟩,
  ⟨102,3,[-1],490⟩,
  ⟨102,4,[-1],802⟩,
  ⟨102,5,[-1],802⟩,
  ⟨102,6,[-1],802⟩,
  ⟨102,7,[-1],802⟩,
  ⟨102,8,[-1],825⟩,
  ⟨102,9,[-1],797⟩
]

private theorem chunk_valid_5 : ∀ r ∈ chunk_5, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_6 : List MiddleCertRecord := [
  ⟨102,10,[-1],817⟩,
  ⟨102,11,[-1],663⟩,
  ⟨102,12,[-1],802⟩,
  ⟨102,13,[-1],802⟩,
  ⟨102,14,[-1],802⟩,
  ⟨102,15,[-1],802⟩,
  ⟨102,16,[-1],925⟩,
  ⟨102,17,[-1],925⟩,
  ⟨102,18,[-1],925⟩,
  ⟨102,19,[-1],925⟩,
  ⟨102,20,[-1],925⟩,
  ⟨102,21,[-1],925⟩,
  ⟨102,22,[-1],925⟩,
  ⟨102,23,[-1],925⟩,
  ⟨102,24,[-1],1168⟩,
  ⟨102,25,[-1],1168⟩
]

private theorem chunk_valid_6 : ∀ r ∈ chunk_6, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_7 : List MiddleCertRecord := [
  ⟨102,26,[-1],1168⟩,
  ⟨102,27,[-1],1168⟩,
  ⟨102,28,[-1],1168⟩,
  ⟨102,29,[-1],1168⟩,
  ⟨102,30,[-1],1168⟩,
  ⟨102,31,[-1],1168⟩,
  ⟨102,32,[-1],490⟩,
  ⟨102,33,[-1],490⟩,
  ⟨102,34,[-1],490⟩,
  ⟨102,35,[-1],490⟩,
  ⟨102,36,[-1],802⟩,
  ⟨102,37,[-1],802⟩,
  ⟨102,38,[-1],802⟩,
  ⟨102,39,[-1],802⟩,
  ⟨102,40,[-1],825⟩,
  ⟨102,41,[-1],797⟩
]

private theorem chunk_valid_7 : ∀ r ∈ chunk_7, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_8 : List MiddleCertRecord := [
  ⟨102,42,[-1],817⟩,
  ⟨102,43,[-1],663⟩,
  ⟨102,44,[-1],802⟩,
  ⟨102,45,[-1],802⟩,
  ⟨102,46,[-1],802⟩,
  ⟨102,47,[-1],802⟩,
  ⟨102,48,[-1],925⟩,
  ⟨102,49,[-1],925⟩,
  ⟨102,50,[-1],925⟩,
  ⟨102,51,[-1],925⟩,
  ⟨102,52,[-1],925⟩,
  ⟨102,53,[-1],925⟩,
  ⟨102,54,[-1],925⟩,
  ⟨102,55,[-1],925⟩,
  ⟨102,56,[-1],1168⟩,
  ⟨102,57,[-1],1168⟩
]

private theorem chunk_valid_8 : ∀ r ∈ chunk_8, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_9 : List MiddleCertRecord := [
  ⟨102,58,[-1],1168⟩,
  ⟨102,59,[-1],1168⟩,
  ⟨102,60,[-1],1168⟩,
  ⟨102,61,[-1],1168⟩,
  ⟨102,62,[-1],1168⟩,
  ⟨102,63,[-1],1168⟩,
  ⟨104,0,[-1],243⟩,
  ⟨104,1,[-1],243⟩,
  ⟨104,2,[-1],243⟩,
  ⟨104,3,[-1],243⟩,
  ⟨104,4,[-1],243⟩,
  ⟨104,5,[-1],243⟩,
  ⟨104,6,[-1],243⟩,
  ⟨104,7,[-1],243⟩,
  ⟨104,8,[-1],266⟩,
  ⟨104,9,[-1],266⟩
]

private theorem chunk_valid_9 : ∀ r ∈ chunk_9, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_10 : List MiddleCertRecord := [
  ⟨104,10,[-1],266⟩,
  ⟨104,11,[-1],266⟩,
  ⟨104,12,[-1],266⟩,
  ⟨104,13,[-1],266⟩,
  ⟨104,14,[-1],266⟩,
  ⟨104,15,[-1],266⟩,
  ⟨104,16,[-1],242⟩,
  ⟨104,17,[-1],242⟩,
  ⟨104,18,[-1],242⟩,
  ⟨104,19,[-1],242⟩,
  ⟨104,20,[-1],245⟩,
  ⟨104,21,[-1],245⟩,
  ⟨104,22,[-1],245⟩,
  ⟨104,23,[-1],245⟩,
  ⟨104,24,[-1],242⟩,
  ⟨104,25,[-1],242⟩
]

private theorem chunk_valid_10 : ∀ r ∈ chunk_10, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_11 : List MiddleCertRecord := [
  ⟨104,26,[-1],242⟩,
  ⟨104,27,[-1],242⟩,
  ⟨104,28,[-1],260⟩,
  ⟨104,29,[-1],253⟩,
  ⟨104,30,[-1],256⟩,
  ⟨104,31,[-1],269⟩,
  ⟨104,32,[-1],243⟩,
  ⟨104,33,[-1],243⟩,
  ⟨104,34,[-1],243⟩,
  ⟨104,35,[-1],243⟩,
  ⟨104,36,[-1],243⟩,
  ⟨104,37,[-1],243⟩,
  ⟨104,38,[-1],243⟩,
  ⟨104,39,[-1],243⟩,
  ⟨104,40,[-1],266⟩,
  ⟨104,41,[-1],266⟩
]

private theorem chunk_valid_11 : ∀ r ∈ chunk_11, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_12 : List MiddleCertRecord := [
  ⟨104,42,[-1],266⟩,
  ⟨104,43,[-1],266⟩,
  ⟨104,44,[-1],266⟩,
  ⟨104,45,[-1],266⟩,
  ⟨104,46,[-1],266⟩,
  ⟨104,47,[-1],266⟩,
  ⟨104,48,[-1],242⟩,
  ⟨104,49,[-1],242⟩,
  ⟨104,50,[-1],242⟩,
  ⟨104,51,[-1],242⟩,
  ⟨104,52,[-1],245⟩,
  ⟨104,53,[-1],245⟩,
  ⟨104,54,[-1],245⟩,
  ⟨104,55,[-1],245⟩,
  ⟨104,56,[-1],242⟩,
  ⟨104,57,[-1],242⟩
]

private theorem chunk_valid_12 : ∀ r ∈ chunk_12, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_13 : List MiddleCertRecord := [
  ⟨104,58,[-1],242⟩,
  ⟨104,59,[-1],242⟩,
  ⟨104,60,[-1],260⟩,
  ⟨104,61,[-1],253⟩,
  ⟨104,62,[-1],256⟩,
  ⟨104,63,[-1],269⟩,
  ⟨105,0,[-1],224⟩,
  ⟨105,1,[-1],224⟩,
  ⟨105,2,[-1],224⟩,
  ⟨105,3,[-1],224⟩,
  ⟨105,4,[-1],799⟩,
  ⟨105,5,[-1],799⟩,
  ⟨105,6,[-1],799⟩,
  ⟨105,7,[-1],799⟩,
  ⟨105,8,[-1],929⟩,
  ⟨105,9,[-1],1121⟩
]

private theorem chunk_valid_13 : ∀ r ∈ chunk_13, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_14 : List MiddleCertRecord := [
  ⟨105,10,[-1],1193⟩,
  ⟨105,11,[-1],669⟩,
  ⟨105,12,[-1],799⟩,
  ⟨105,13,[-1],799⟩,
  ⟨105,14,[-1],799⟩,
  ⟨105,15,[-1],799⟩,
  ⟨105,16,[-1],1175⟩,
  ⟨105,17,[-1],1175⟩,
  ⟨105,18,[-1],1175⟩,
  ⟨105,19,[-1],1175⟩,
  ⟨105,20,[-1],1175⟩,
  ⟨105,21,[-1],1175⟩,
  ⟨105,22,[-1],1175⟩,
  ⟨105,23,[-1],1175⟩,
  ⟨105,24,[-1],997⟩,
  ⟨105,25,[-1],997⟩
]

private theorem chunk_valid_14 : ∀ r ∈ chunk_14, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_15 : List MiddleCertRecord := [
  ⟨105,26,[-1],997⟩,
  ⟨105,27,[-1],997⟩,
  ⟨105,28,[-1],997⟩,
  ⟨105,29,[-1],997⟩,
  ⟨105,30,[-1],997⟩,
  ⟨105,31,[-1],997⟩,
  ⟨105,32,[-1],224⟩,
  ⟨105,33,[-1],224⟩,
  ⟨105,34,[-1],224⟩,
  ⟨105,35,[-1],224⟩,
  ⟨105,36,[-1],799⟩,
  ⟨105,37,[-1],799⟩,
  ⟨105,38,[-1],799⟩,
  ⟨105,39,[-1],799⟩,
  ⟨105,40,[-1],929⟩,
  ⟨105,41,[-1],1121⟩
]

private theorem chunk_valid_15 : ∀ r ∈ chunk_15, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_16 : List MiddleCertRecord := [
  ⟨105,42,[-1],1193⟩,
  ⟨105,43,[-1],669⟩,
  ⟨105,44,[-1],799⟩,
  ⟨105,45,[-1],799⟩,
  ⟨105,46,[-1],799⟩,
  ⟨105,47,[-1],799⟩,
  ⟨105,48,[-1],1175⟩,
  ⟨105,49,[-1],1175⟩,
  ⟨105,50,[-1],1175⟩,
  ⟨105,51,[-1],1175⟩,
  ⟨105,52,[-1],1175⟩,
  ⟨105,53,[-1],1175⟩,
  ⟨105,54,[-1],1175⟩,
  ⟨105,55,[-1],1175⟩,
  ⟨105,56,[-1],997⟩,
  ⟨105,57,[-1],997⟩
]

private theorem chunk_valid_16 : ∀ r ∈ chunk_16, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_17 : List MiddleCertRecord := [
  ⟨105,58,[-1],997⟩,
  ⟨105,59,[-1],997⟩,
  ⟨105,60,[-1],997⟩,
  ⟨105,61,[-1],997⟩,
  ⟨105,62,[-1],997⟩,
  ⟨105,63,[-1],997⟩,
  ⟨107,0,[-1],237⟩,
  ⟨107,1,[-1],267⟩,
  ⟨107,2,[-1],246⟩,
  ⟨107,3,[-1],270⟩,
  ⟨107,4,[-1],237⟩,
  ⟨107,5,[-1],267⟩,
  ⟨107,6,[-1],254⟩,
  ⟨107,7,[-1],252⟩,
  ⟨107,8,[-1],237⟩,
  ⟨107,9,[-1],267⟩
]

private theorem chunk_valid_17 : ∀ r ∈ chunk_17, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_18 : List MiddleCertRecord := [
  ⟨107,10,[-1],246⟩,
  ⟨107,11,[-1],251⟩,
  ⟨107,12,[-1],237⟩,
  ⟨107,13,[-1],267⟩,
  ⟨107,14,[-1],246⟩,
  ⟨107,15,[-1],263⟩,
  ⟨108,0,[-1],467⟩,
  ⟨108,1,[-1],469⟩,
  ⟨108,2,[-1],468⟩,
  ⟨108,3,[-1],468⟩,
  ⟨108,4,[-1],1082⟩,
  ⟨108,5,[-1],1032⟩,
  ⟨108,6,[-1],905⟩,
  ⟨108,7,[-1],614⟩,
  ⟨108,8,[-1],716⟩,
  ⟨108,9,[-1],720⟩
]

private theorem chunk_valid_18 : ∀ r ∈ chunk_18, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_19 : List MiddleCertRecord := [
  ⟨108,10,[-1],719⟩,
  ⟨108,11,[-1],719⟩,
  ⟨108,12,[-1],1163⟩,
  ⟨108,13,[-1],1165⟩,
  ⟨108,14,[-1],1164⟩,
  ⟨108,15,[-1],1164⟩,
  ⟨110,0,[-1],234⟩,
  ⟨110,1,[-1],271⟩,
  ⟨110,2,[-1],238⟩,
  ⟨110,3,[-1],272⟩,
  ⟨110,4,[-1],234⟩,
  ⟨110,5,[-1],271⟩,
  ⟨110,6,[-1],249⟩,
  ⟨110,7,[-1],257⟩,
  ⟨110,8,[-1],234⟩,
  ⟨110,9,[-1],271⟩
]

private theorem chunk_valid_19 : ∀ r ∈ chunk_19, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_20 : List MiddleCertRecord := [
  ⟨110,10,[-1],238⟩,
  ⟨110,11,[-1],248⟩,
  ⟨110,12,[-1],234⟩,
  ⟨110,13,[-1],271⟩,
  ⟨110,14,[-1],238⟩,
  ⟨110,15,[-1],264⟩,
  ⟨111,0,[-1],8⟩,
  ⟨111,1,[-1],8⟩,
  ⟨111,2,[-1],8⟩,
  ⟨111,3,[-1],8⟩,
  ⟨111,4,[-1],592⟩,
  ⟨111,5,[-1],705⟩,
  ⟨111,6,[-1],599⟩,
  ⟨111,7,[-1],1002⟩,
  ⟨111,8,[-1],763⟩,
  ⟨111,9,[-1],763⟩
]

private theorem chunk_valid_20 : ∀ r ∈ chunk_20, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_21 : List MiddleCertRecord := [
  ⟨111,10,[-1],763⟩,
  ⟨111,11,[-1],763⟩,
  ⟨111,12,[-1],687⟩,
  ⟨111,13,[-1],687⟩,
  ⟨111,14,[-1],687⟩,
  ⟨111,15,[-1],687⟩,
  ⟨112,0,[-1],449⟩,
  ⟨112,1,[-1],449⟩,
  ⟨112,2,[-1],449⟩,
  ⟨112,3,[-1],449⟩,
  ⟨112,4,[-1],605⟩,
  ⟨112,5,[-1],827⟩,
  ⟨112,6,[-1],924⟩,
  ⟨112,7,[-1],926⟩,
  ⟨112,8,[-1],733⟩,
  ⟨112,9,[-1],736⟩
]

private theorem chunk_valid_21 : ∀ r ∈ chunk_21, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_22 : List MiddleCertRecord := [
  ⟨112,10,[-1],734⟩,
  ⟨112,11,[-1],734⟩,
  ⟨112,12,[-1],1151⟩,
  ⟨112,13,[-1],1152⟩,
  ⟨112,14,[-1],1151⟩,
  ⟨112,15,[-1],1151⟩,
  ⟨114,0,[-1],335⟩,
  ⟨114,1,[-1],340⟩,
  ⟨114,2,[-1],338⟩,
  ⟨114,3,[-1],336⟩,
  ⟨114,4,[-1],335⟩,
  ⟨114,5,[-1],340⟩,
  ⟨114,6,[-1],338⟩,
  ⟨114,7,[-1],342⟩,
  ⟨114,8,[-1],233⟩,
  ⟨114,9,[-1],261⟩
]

private theorem chunk_valid_22 : ∀ r ∈ chunk_22, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_23 : List MiddleCertRecord := [
  ⟨114,10,[-1],244⟩,
  ⟨114,11,[-1],235⟩,
  ⟨114,12,[-1],233⟩,
  ⟨114,13,[-1],261⟩,
  ⟨114,14,[-1],244⟩,
  ⟨114,15,[-1],250⟩,
  ⟨114,16,[-1],834⟩,
  ⟨114,17,[-1],845⟩,
  ⟨114,18,[-1],839⟩,
  ⟨114,19,[-1],835⟩,
  ⟨114,20,[-1],834⟩,
  ⟨114,21,[-1],845⟩,
  ⟨114,22,[-1],839⟩,
  ⟨114,23,[-1],841⟩,
  ⟨114,24,[-1],1106⟩,
  ⟨114,25,[-1],1111⟩
]

private theorem chunk_valid_23 : ∀ r ∈ chunk_23, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_24 : List MiddleCertRecord := [
  ⟨114,26,[-1],1109⟩,
  ⟨114,27,[-1],1107⟩,
  ⟨114,28,[-1],1106⟩,
  ⟨114,29,[-1],1111⟩,
  ⟨114,30,[-1],1109⟩,
  ⟨114,31,[-1],1113⟩,
  ⟨116,0,[-1],236⟩,
  ⟨116,1,[-1],262⟩,
  ⟨116,2,[-1],235⟩,
  ⟨116,3,[-1],235⟩,
  ⟨116,4,[-1],236⟩,
  ⟨116,5,[-1],262⟩,
  ⟨116,6,[-1],235⟩,
  ⟨116,7,[-1],235⟩,
  ⟨116,8,[-1],236⟩,
  ⟨116,9,[-1],262⟩
]

private theorem chunk_valid_24 : ∀ r ∈ chunk_24, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_25 : List MiddleCertRecord := [
  ⟨116,10,[-1],235⟩,
  ⟨116,11,[-1],235⟩,
  ⟨116,12,[-1],236⟩,
  ⟨116,13,[-1],262⟩,
  ⟨116,14,[-1],235⟩,
  ⟨116,15,[-1],235⟩,
  ⟨116,16,[-1],543⟩,
  ⟨116,17,[-1],561⟩,
  ⟨116,18,[-1],542⟩,
  ⟨116,19,[-1],542⟩,
  ⟨116,20,[-1],543⟩,
  ⟨116,21,[-1],561⟩,
  ⟨116,22,[-1],542⟩,
  ⟨116,23,[-1],542⟩,
  ⟨116,24,[-1],956⟩,
  ⟨116,25,[-1],974⟩
]

private theorem chunk_valid_25 : ∀ r ∈ chunk_25, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_26 : List MiddleCertRecord := [
  ⟨116,26,[-1],955⟩,
  ⟨116,27,[-1],955⟩,
  ⟨116,28,[-1],956⟩,
  ⟨116,29,[-1],974⟩,
  ⟨116,30,[-1],955⟩,
  ⟨116,31,[-1],955⟩,
  ⟨116,32,[-1],236⟩,
  ⟨116,33,[-1],262⟩,
  ⟨116,34,[-1],241⟩,
  ⟨116,35,[-1],268⟩,
  ⟨116,36,[-1],236⟩,
  ⟨116,37,[-1],262⟩,
  ⟨116,38,[-1],241⟩,
  ⟨116,39,[-1],268⟩,
  ⟨116,40,[-1],236⟩,
  ⟨116,41,[-1],262⟩
]

private theorem chunk_valid_26 : ∀ r ∈ chunk_26, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_27 : List MiddleCertRecord := [
  ⟨116,42,[-1],241⟩,
  ⟨116,43,[-1],255⟩,
  ⟨116,44,[-1],236⟩,
  ⟨116,45,[-1],262⟩,
  ⟨116,46,[-1],241⟩,
  ⟨116,47,[-1],255⟩,
  ⟨116,48,[-1],543⟩,
  ⟨116,49,[-1],561⟩,
  ⟨116,50,[-1],547⟩,
  ⟨116,51,[-1],557⟩,
  ⟨116,52,[-1],543⟩,
  ⟨116,53,[-1],561⟩,
  ⟨116,54,[-1],547⟩,
  ⟨116,55,[-1],557⟩,
  ⟨116,56,[-1],956⟩,
  ⟨116,57,[-1],974⟩
]

private theorem chunk_valid_27 : ∀ r ∈ chunk_27, middleCertRecordValid middleCertData r := by
  decide +kernel

private def chunk_28 : List MiddleCertRecord := [
  ⟨116,58,[-1],960⟩,
  ⟨116,59,[-1],971⟩,
  ⟨116,60,[-1],956⟩,
  ⟨116,61,[-1],974⟩,
  ⟨116,62,[-1],960⟩,
  ⟨116,63,[-1],971⟩
]

private theorem chunk_valid_28 : ∀ r ∈ chunk_28, middleCertRecordValid middleCertData r := by
  decide +kernel

private theorem chunks_eq : [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25, chunk_26, chunk_27, chunk_28].flatten = selectedRecords := by
  decide +kernel

private theorem chunks_valid : ∀ rs ∈ [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25, chunk_26, chunk_27, chunk_28], ∀ r ∈ rs, middleCertRecordValid middleCertData r := by
  simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨chunk_valid_0, chunk_valid_1, chunk_valid_2, chunk_valid_3, chunk_valid_4, chunk_valid_5, chunk_valid_6, chunk_valid_7, chunk_valid_8, chunk_valid_9, chunk_valid_10, chunk_valid_11, chunk_valid_12, chunk_valid_13, chunk_valid_14, chunk_valid_15, chunk_valid_16, chunk_valid_17, chunk_valid_18, chunk_valid_19, chunk_valid_20, chunk_valid_21, chunk_valid_22, chunk_valid_23, chunk_valid_24, chunk_valid_25, chunk_valid_26, chunk_valid_27, chunk_valid_28, List.forall_mem_nil _⟩

private theorem records_valid :
    ∀ r ∈ selectedRecords, middleCertRecordValid middleCertData r := by
  intro r hr
  rw [← chunks_eq] at hr
  rcases List.mem_flatten.mp hr with ⟨rs, hrs, hr⟩
  exact chunks_valid rs hrs r hr

private def goalRecords_97 : List MiddleCertRecord := [
  ⟨98,4,[-1],406⟩,
  ⟨98,6,[-1],734⟩,
  ⟨98,7,[-1],1135⟩,
  ⟨98,12,[-1],739⟩,
  ⟨98,13,[-1],739⟩,
  ⟨98,14,[-1],739⟩
]

private theorem goal_subset_97 : ∀ r ∈ goalRecords_97, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_97 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 98)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 98) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_97, r.goal = 98 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_97, r.goal = 98 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_97 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 98)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 98) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 98 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 98 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_97 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_97 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_97 r hr, hg, hb, hp⟩

private def goalRecords_98 : List MiddleCertRecord := [
  ⟨99,1,[-1],407⟩,
  ⟨99,2,[-1],739⟩,
  ⟨99,3,[-1],739⟩,
  ⟨99,7,[-1],739⟩,
  ⟨99,8,[-1],745⟩,
  ⟨99,9,[-1],745⟩,
  ⟨99,11,[-1],1137⟩,
  ⟨99,13,[-1],1138⟩,
  ⟨99,17,[-1],407⟩,
  ⟨99,18,[-1],739⟩,
  ⟨99,19,[-1],739⟩,
  ⟨99,23,[-1],739⟩,
  ⟨99,24,[-1],744⟩,
  ⟨99,25,[-1],744⟩,
  ⟨99,27,[-1],1137⟩,
  ⟨99,29,[-1],1136⟩
]

private theorem goal_subset_98 : ∀ r ∈ goalRecords_98, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_98 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 99)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 99) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_98, r.goal = 99 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_98, r.goal = 99 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_98 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 99)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 99) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 99 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 99 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_98 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_98 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_98 r hr, hg, hb, hp⟩

private def goalRecords_99 : List MiddleCertRecord := [

]

private theorem goal_subset_99 : ∀ r ∈ goalRecords_99, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_99 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 100)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 100) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_99, r.goal = 100 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_99, r.goal = 100 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_99 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 100)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 100) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 100 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 100 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_99 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_99 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_99 r hr, hg, hb, hp⟩

private def goalRecords_100 : List MiddleCertRecord := [
  ⟨101,0,[-1],247⟩,
  ⟨101,1,[-1],247⟩,
  ⟨101,2,[-1],1050⟩,
  ⟨101,3,[-1],993⟩,
  ⟨101,4,[-1],247⟩,
  ⟨101,5,[-1],247⟩,
  ⟨101,6,[-1],1050⟩,
  ⟨101,7,[-1],993⟩,
  ⟨101,8,[-1],259⟩,
  ⟨101,9,[-1],259⟩,
  ⟨101,10,[-1],1052⟩,
  ⟨101,11,[-1],994⟩,
  ⟨101,12,[-1],259⟩,
  ⟨101,13,[-1],259⟩,
  ⟨101,14,[-1],1052⟩,
  ⟨101,15,[-1],994⟩,
  ⟨101,16,[-1],239⟩,
  ⟨101,17,[-1],239⟩,
  ⟨101,18,[-1],1048⟩,
  ⟨101,19,[-1],991⟩,
  ⟨101,20,[-1],240⟩,
  ⟨101,21,[-1],240⟩,
  ⟨101,22,[-1],1049⟩,
  ⟨101,23,[-1],992⟩,
  ⟨101,24,[-1],239⟩,
  ⟨101,25,[-1],239⟩,
  ⟨101,26,[-1],1048⟩,
  ⟨101,27,[-1],991⟩,
  ⟨101,28,[-1],265⟩,
  ⟨101,29,[-1],258⟩,
  ⟨101,30,[-1],1051⟩,
  ⟨101,31,[-1],995⟩,
  ⟨101,32,[-1],1090⟩,
  ⟨101,33,[-1],1090⟩,
  ⟨101,34,[-1],1090⟩,
  ⟨101,35,[-1],993⟩,
  ⟨101,36,[-1],1090⟩,
  ⟨101,37,[-1],1090⟩,
  ⟨101,38,[-1],1090⟩,
  ⟨101,39,[-1],993⟩,
  ⟨101,40,[-1],1093⟩,
  ⟨101,41,[-1],1093⟩,
  ⟨101,42,[-1],1093⟩,
  ⟨101,43,[-1],994⟩,
  ⟨101,44,[-1],1093⟩,
  ⟨101,45,[-1],1093⟩,
  ⟨101,46,[-1],1093⟩,
  ⟨101,47,[-1],994⟩,
  ⟨101,48,[-1],1088⟩,
  ⟨101,49,[-1],1088⟩,
  ⟨101,50,[-1],1088⟩,
  ⟨101,51,[-1],991⟩,
  ⟨101,52,[-1],1089⟩,
  ⟨101,53,[-1],1089⟩,
  ⟨101,54,[-1],1089⟩,
  ⟨101,55,[-1],992⟩,
  ⟨101,56,[-1],1088⟩,
  ⟨101,57,[-1],1088⟩,
  ⟨101,58,[-1],1088⟩,
  ⟨101,59,[-1],991⟩,
  ⟨101,60,[-1],1094⟩,
  ⟨101,61,[-1],1092⟩,
  ⟨101,62,[-1],1091⟩,
  ⟨101,63,[-1],995⟩
]

private theorem goal_subset_100 : ∀ r ∈ goalRecords_100, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_100 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 101)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 101) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_100, r.goal = 101 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_100, r.goal = 101 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_100 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 101)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 101) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 101 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 101 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_100 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_100 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_100 r hr, hg, hb, hp⟩

private def goalRecords_101 : List MiddleCertRecord := [
  ⟨102,0,[-1],490⟩,
  ⟨102,1,[-1],490⟩,
  ⟨102,2,[-1],490⟩,
  ⟨102,3,[-1],490⟩,
  ⟨102,4,[-1],802⟩,
  ⟨102,5,[-1],802⟩,
  ⟨102,6,[-1],802⟩,
  ⟨102,7,[-1],802⟩,
  ⟨102,8,[-1],825⟩,
  ⟨102,9,[-1],797⟩,
  ⟨102,10,[-1],817⟩,
  ⟨102,11,[-1],663⟩,
  ⟨102,12,[-1],802⟩,
  ⟨102,13,[-1],802⟩,
  ⟨102,14,[-1],802⟩,
  ⟨102,15,[-1],802⟩,
  ⟨102,16,[-1],925⟩,
  ⟨102,17,[-1],925⟩,
  ⟨102,18,[-1],925⟩,
  ⟨102,19,[-1],925⟩,
  ⟨102,20,[-1],925⟩,
  ⟨102,21,[-1],925⟩,
  ⟨102,22,[-1],925⟩,
  ⟨102,23,[-1],925⟩,
  ⟨102,24,[-1],1168⟩,
  ⟨102,25,[-1],1168⟩,
  ⟨102,26,[-1],1168⟩,
  ⟨102,27,[-1],1168⟩,
  ⟨102,28,[-1],1168⟩,
  ⟨102,29,[-1],1168⟩,
  ⟨102,30,[-1],1168⟩,
  ⟨102,31,[-1],1168⟩,
  ⟨102,32,[-1],490⟩,
  ⟨102,33,[-1],490⟩,
  ⟨102,34,[-1],490⟩,
  ⟨102,35,[-1],490⟩,
  ⟨102,36,[-1],802⟩,
  ⟨102,37,[-1],802⟩,
  ⟨102,38,[-1],802⟩,
  ⟨102,39,[-1],802⟩,
  ⟨102,40,[-1],825⟩,
  ⟨102,41,[-1],797⟩,
  ⟨102,42,[-1],817⟩,
  ⟨102,43,[-1],663⟩,
  ⟨102,44,[-1],802⟩,
  ⟨102,45,[-1],802⟩,
  ⟨102,46,[-1],802⟩,
  ⟨102,47,[-1],802⟩,
  ⟨102,48,[-1],925⟩,
  ⟨102,49,[-1],925⟩,
  ⟨102,50,[-1],925⟩,
  ⟨102,51,[-1],925⟩,
  ⟨102,52,[-1],925⟩,
  ⟨102,53,[-1],925⟩,
  ⟨102,54,[-1],925⟩,
  ⟨102,55,[-1],925⟩,
  ⟨102,56,[-1],1168⟩,
  ⟨102,57,[-1],1168⟩,
  ⟨102,58,[-1],1168⟩,
  ⟨102,59,[-1],1168⟩,
  ⟨102,60,[-1],1168⟩,
  ⟨102,61,[-1],1168⟩,
  ⟨102,62,[-1],1168⟩,
  ⟨102,63,[-1],1168⟩
]

private theorem goal_subset_101 : ∀ r ∈ goalRecords_101, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_101 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 102)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 102) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_101, r.goal = 102 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_101, r.goal = 102 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_101 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 102)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 102) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 102 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 102 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_101 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_101 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_101 r hr, hg, hb, hp⟩

private def goalRecords_102 : List MiddleCertRecord := [

]

private theorem goal_subset_102 : ∀ r ∈ goalRecords_102, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_102 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 103)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 103) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_102, r.goal = 103 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_102, r.goal = 103 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_102 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 103)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 103) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 103 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 103 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_102 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_102 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_102 r hr, hg, hb, hp⟩

private def goalRecords_103 : List MiddleCertRecord := [
  ⟨104,0,[-1],243⟩,
  ⟨104,1,[-1],243⟩,
  ⟨104,2,[-1],243⟩,
  ⟨104,3,[-1],243⟩,
  ⟨104,4,[-1],243⟩,
  ⟨104,5,[-1],243⟩,
  ⟨104,6,[-1],243⟩,
  ⟨104,7,[-1],243⟩,
  ⟨104,8,[-1],266⟩,
  ⟨104,9,[-1],266⟩,
  ⟨104,10,[-1],266⟩,
  ⟨104,11,[-1],266⟩,
  ⟨104,12,[-1],266⟩,
  ⟨104,13,[-1],266⟩,
  ⟨104,14,[-1],266⟩,
  ⟨104,15,[-1],266⟩,
  ⟨104,16,[-1],242⟩,
  ⟨104,17,[-1],242⟩,
  ⟨104,18,[-1],242⟩,
  ⟨104,19,[-1],242⟩,
  ⟨104,20,[-1],245⟩,
  ⟨104,21,[-1],245⟩,
  ⟨104,22,[-1],245⟩,
  ⟨104,23,[-1],245⟩,
  ⟨104,24,[-1],242⟩,
  ⟨104,25,[-1],242⟩,
  ⟨104,26,[-1],242⟩,
  ⟨104,27,[-1],242⟩,
  ⟨104,28,[-1],260⟩,
  ⟨104,29,[-1],253⟩,
  ⟨104,30,[-1],256⟩,
  ⟨104,31,[-1],269⟩,
  ⟨104,32,[-1],243⟩,
  ⟨104,33,[-1],243⟩,
  ⟨104,34,[-1],243⟩,
  ⟨104,35,[-1],243⟩,
  ⟨104,36,[-1],243⟩,
  ⟨104,37,[-1],243⟩,
  ⟨104,38,[-1],243⟩,
  ⟨104,39,[-1],243⟩,
  ⟨104,40,[-1],266⟩,
  ⟨104,41,[-1],266⟩,
  ⟨104,42,[-1],266⟩,
  ⟨104,43,[-1],266⟩,
  ⟨104,44,[-1],266⟩,
  ⟨104,45,[-1],266⟩,
  ⟨104,46,[-1],266⟩,
  ⟨104,47,[-1],266⟩,
  ⟨104,48,[-1],242⟩,
  ⟨104,49,[-1],242⟩,
  ⟨104,50,[-1],242⟩,
  ⟨104,51,[-1],242⟩,
  ⟨104,52,[-1],245⟩,
  ⟨104,53,[-1],245⟩,
  ⟨104,54,[-1],245⟩,
  ⟨104,55,[-1],245⟩,
  ⟨104,56,[-1],242⟩,
  ⟨104,57,[-1],242⟩,
  ⟨104,58,[-1],242⟩,
  ⟨104,59,[-1],242⟩,
  ⟨104,60,[-1],260⟩,
  ⟨104,61,[-1],253⟩,
  ⟨104,62,[-1],256⟩,
  ⟨104,63,[-1],269⟩
]

private theorem goal_subset_103 : ∀ r ∈ goalRecords_103, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_103 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 104)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 104) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_103, r.goal = 104 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_103, r.goal = 104 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_103 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 104)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 104) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 104 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 104 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_103 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_103 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_103 r hr, hg, hb, hp⟩

private def goalRecords_104 : List MiddleCertRecord := [
  ⟨105,0,[-1],224⟩,
  ⟨105,1,[-1],224⟩,
  ⟨105,2,[-1],224⟩,
  ⟨105,3,[-1],224⟩,
  ⟨105,4,[-1],799⟩,
  ⟨105,5,[-1],799⟩,
  ⟨105,6,[-1],799⟩,
  ⟨105,7,[-1],799⟩,
  ⟨105,8,[-1],929⟩,
  ⟨105,9,[-1],1121⟩,
  ⟨105,10,[-1],1193⟩,
  ⟨105,11,[-1],669⟩,
  ⟨105,12,[-1],799⟩,
  ⟨105,13,[-1],799⟩,
  ⟨105,14,[-1],799⟩,
  ⟨105,15,[-1],799⟩,
  ⟨105,16,[-1],1175⟩,
  ⟨105,17,[-1],1175⟩,
  ⟨105,18,[-1],1175⟩,
  ⟨105,19,[-1],1175⟩,
  ⟨105,20,[-1],1175⟩,
  ⟨105,21,[-1],1175⟩,
  ⟨105,22,[-1],1175⟩,
  ⟨105,23,[-1],1175⟩,
  ⟨105,24,[-1],997⟩,
  ⟨105,25,[-1],997⟩,
  ⟨105,26,[-1],997⟩,
  ⟨105,27,[-1],997⟩,
  ⟨105,28,[-1],997⟩,
  ⟨105,29,[-1],997⟩,
  ⟨105,30,[-1],997⟩,
  ⟨105,31,[-1],997⟩,
  ⟨105,32,[-1],224⟩,
  ⟨105,33,[-1],224⟩,
  ⟨105,34,[-1],224⟩,
  ⟨105,35,[-1],224⟩,
  ⟨105,36,[-1],799⟩,
  ⟨105,37,[-1],799⟩,
  ⟨105,38,[-1],799⟩,
  ⟨105,39,[-1],799⟩,
  ⟨105,40,[-1],929⟩,
  ⟨105,41,[-1],1121⟩,
  ⟨105,42,[-1],1193⟩,
  ⟨105,43,[-1],669⟩,
  ⟨105,44,[-1],799⟩,
  ⟨105,45,[-1],799⟩,
  ⟨105,46,[-1],799⟩,
  ⟨105,47,[-1],799⟩,
  ⟨105,48,[-1],1175⟩,
  ⟨105,49,[-1],1175⟩,
  ⟨105,50,[-1],1175⟩,
  ⟨105,51,[-1],1175⟩,
  ⟨105,52,[-1],1175⟩,
  ⟨105,53,[-1],1175⟩,
  ⟨105,54,[-1],1175⟩,
  ⟨105,55,[-1],1175⟩,
  ⟨105,56,[-1],997⟩,
  ⟨105,57,[-1],997⟩,
  ⟨105,58,[-1],997⟩,
  ⟨105,59,[-1],997⟩,
  ⟨105,60,[-1],997⟩,
  ⟨105,61,[-1],997⟩,
  ⟨105,62,[-1],997⟩,
  ⟨105,63,[-1],997⟩
]

private theorem goal_subset_104 : ∀ r ∈ goalRecords_104, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_104 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 105)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 105) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_104, r.goal = 105 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_104, r.goal = 105 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_104 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 105)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 105) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 105 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 105 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_104 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_104 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_104 r hr, hg, hb, hp⟩

private def goalRecords_105 : List MiddleCertRecord := [

]

private theorem goal_subset_105 : ∀ r ∈ goalRecords_105, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_105 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 106)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 106) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_105, r.goal = 106 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_105, r.goal = 106 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_105 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 106)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 106) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 106 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 106 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_105 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_105 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_105 r hr, hg, hb, hp⟩

private def goalRecords_106 : List MiddleCertRecord := [
  ⟨107,0,[-1],237⟩,
  ⟨107,1,[-1],267⟩,
  ⟨107,2,[-1],246⟩,
  ⟨107,3,[-1],270⟩,
  ⟨107,4,[-1],237⟩,
  ⟨107,5,[-1],267⟩,
  ⟨107,6,[-1],254⟩,
  ⟨107,7,[-1],252⟩,
  ⟨107,8,[-1],237⟩,
  ⟨107,9,[-1],267⟩,
  ⟨107,10,[-1],246⟩,
  ⟨107,11,[-1],251⟩,
  ⟨107,12,[-1],237⟩,
  ⟨107,13,[-1],267⟩,
  ⟨107,14,[-1],246⟩,
  ⟨107,15,[-1],263⟩
]

private theorem goal_subset_106 : ∀ r ∈ goalRecords_106, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_106 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 107)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 107) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_106, r.goal = 107 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_106, r.goal = 107 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_106 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 107)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 107) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 107 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 107 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_106 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_106 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_106 r hr, hg, hb, hp⟩

private def goalRecords_107 : List MiddleCertRecord := [
  ⟨108,0,[-1],467⟩,
  ⟨108,1,[-1],469⟩,
  ⟨108,2,[-1],468⟩,
  ⟨108,3,[-1],468⟩,
  ⟨108,4,[-1],1082⟩,
  ⟨108,5,[-1],1032⟩,
  ⟨108,6,[-1],905⟩,
  ⟨108,7,[-1],614⟩,
  ⟨108,8,[-1],716⟩,
  ⟨108,9,[-1],720⟩,
  ⟨108,10,[-1],719⟩,
  ⟨108,11,[-1],719⟩,
  ⟨108,12,[-1],1163⟩,
  ⟨108,13,[-1],1165⟩,
  ⟨108,14,[-1],1164⟩,
  ⟨108,15,[-1],1164⟩
]

private theorem goal_subset_107 : ∀ r ∈ goalRecords_107, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_107 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 108)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 108) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_107, r.goal = 108 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_107, r.goal = 108 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_107 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 108)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 108) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 108 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 108 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_107 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_107 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_107 r hr, hg, hb, hp⟩

private def goalRecords_108 : List MiddleCertRecord := [

]

private theorem goal_subset_108 : ∀ r ∈ goalRecords_108, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_108 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 109)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 109) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_108, r.goal = 109 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_108, r.goal = 109 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_108 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 109)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 109) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 109 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 109 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_108 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_108 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_108 r hr, hg, hb, hp⟩

private def goalRecords_109 : List MiddleCertRecord := [
  ⟨110,0,[-1],234⟩,
  ⟨110,1,[-1],271⟩,
  ⟨110,2,[-1],238⟩,
  ⟨110,3,[-1],272⟩,
  ⟨110,4,[-1],234⟩,
  ⟨110,5,[-1],271⟩,
  ⟨110,6,[-1],249⟩,
  ⟨110,7,[-1],257⟩,
  ⟨110,8,[-1],234⟩,
  ⟨110,9,[-1],271⟩,
  ⟨110,10,[-1],238⟩,
  ⟨110,11,[-1],248⟩,
  ⟨110,12,[-1],234⟩,
  ⟨110,13,[-1],271⟩,
  ⟨110,14,[-1],238⟩,
  ⟨110,15,[-1],264⟩
]

private theorem goal_subset_109 : ∀ r ∈ goalRecords_109, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_109 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 110)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 110) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_109, r.goal = 110 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_109, r.goal = 110 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_109 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 110)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 110) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 110 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 110 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_109 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_109 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_109 r hr, hg, hb, hp⟩

private def goalRecords_110 : List MiddleCertRecord := [
  ⟨111,0,[-1],8⟩,
  ⟨111,1,[-1],8⟩,
  ⟨111,2,[-1],8⟩,
  ⟨111,3,[-1],8⟩,
  ⟨111,4,[-1],592⟩,
  ⟨111,5,[-1],705⟩,
  ⟨111,6,[-1],599⟩,
  ⟨111,7,[-1],1002⟩,
  ⟨111,8,[-1],763⟩,
  ⟨111,9,[-1],763⟩,
  ⟨111,10,[-1],763⟩,
  ⟨111,11,[-1],763⟩,
  ⟨111,12,[-1],687⟩,
  ⟨111,13,[-1],687⟩,
  ⟨111,14,[-1],687⟩,
  ⟨111,15,[-1],687⟩
]

private theorem goal_subset_110 : ∀ r ∈ goalRecords_110, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_110 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 111)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 111) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_110, r.goal = 111 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_110, r.goal = 111 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_110 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 111)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 111) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 111 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 111 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_110 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_110 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_110 r hr, hg, hb, hp⟩

private def goalRecords_111 : List MiddleCertRecord := [
  ⟨112,0,[-1],449⟩,
  ⟨112,1,[-1],449⟩,
  ⟨112,2,[-1],449⟩,
  ⟨112,3,[-1],449⟩,
  ⟨112,4,[-1],605⟩,
  ⟨112,5,[-1],827⟩,
  ⟨112,6,[-1],924⟩,
  ⟨112,7,[-1],926⟩,
  ⟨112,8,[-1],733⟩,
  ⟨112,9,[-1],736⟩,
  ⟨112,10,[-1],734⟩,
  ⟨112,11,[-1],734⟩,
  ⟨112,12,[-1],1151⟩,
  ⟨112,13,[-1],1152⟩,
  ⟨112,14,[-1],1151⟩,
  ⟨112,15,[-1],1151⟩
]

private theorem goal_subset_111 : ∀ r ∈ goalRecords_111, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_111 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 112)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 112) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_111, r.goal = 112 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_111, r.goal = 112 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_111 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 112)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 112) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 112 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 112 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_111 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_111 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_111 r hr, hg, hb, hp⟩

private def goalRecords_112 : List MiddleCertRecord := [

]

private theorem goal_subset_112 : ∀ r ∈ goalRecords_112, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_112 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 113)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 113) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_112, r.goal = 113 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_112, r.goal = 113 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_112 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 113)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 113) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 113 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 113 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_112 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_112 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_112 r hr, hg, hb, hp⟩

private def goalRecords_113 : List MiddleCertRecord := [
  ⟨114,0,[-1],335⟩,
  ⟨114,1,[-1],340⟩,
  ⟨114,2,[-1],338⟩,
  ⟨114,3,[-1],336⟩,
  ⟨114,4,[-1],335⟩,
  ⟨114,5,[-1],340⟩,
  ⟨114,6,[-1],338⟩,
  ⟨114,7,[-1],342⟩,
  ⟨114,8,[-1],233⟩,
  ⟨114,9,[-1],261⟩,
  ⟨114,10,[-1],244⟩,
  ⟨114,11,[-1],235⟩,
  ⟨114,12,[-1],233⟩,
  ⟨114,13,[-1],261⟩,
  ⟨114,14,[-1],244⟩,
  ⟨114,15,[-1],250⟩,
  ⟨114,16,[-1],834⟩,
  ⟨114,17,[-1],845⟩,
  ⟨114,18,[-1],839⟩,
  ⟨114,19,[-1],835⟩,
  ⟨114,20,[-1],834⟩,
  ⟨114,21,[-1],845⟩,
  ⟨114,22,[-1],839⟩,
  ⟨114,23,[-1],841⟩,
  ⟨114,24,[-1],1106⟩,
  ⟨114,25,[-1],1111⟩,
  ⟨114,26,[-1],1109⟩,
  ⟨114,27,[-1],1107⟩,
  ⟨114,28,[-1],1106⟩,
  ⟨114,29,[-1],1111⟩,
  ⟨114,30,[-1],1109⟩,
  ⟨114,31,[-1],1113⟩
]

private theorem goal_subset_113 : ∀ r ∈ goalRecords_113, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_113 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 114)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 114) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_113, r.goal = 114 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_113, r.goal = 114 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_113 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 114)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 114) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 114 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 114 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_113 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_113 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_113 r hr, hg, hb, hp⟩

private def goalRecords_114 : List MiddleCertRecord := [

]

private theorem goal_subset_114 : ∀ r ∈ goalRecords_114, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_114 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 115)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 115) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_114, r.goal = 115 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_114, r.goal = 115 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_114 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 115)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 115) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 115 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 115 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_114 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_114 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_114 r hr, hg, hb, hp⟩

private def goalRecords_115 : List MiddleCertRecord := [
  ⟨116,0,[-1],236⟩,
  ⟨116,1,[-1],262⟩,
  ⟨116,2,[-1],235⟩,
  ⟨116,3,[-1],235⟩,
  ⟨116,4,[-1],236⟩,
  ⟨116,5,[-1],262⟩,
  ⟨116,6,[-1],235⟩,
  ⟨116,7,[-1],235⟩,
  ⟨116,8,[-1],236⟩,
  ⟨116,9,[-1],262⟩,
  ⟨116,10,[-1],235⟩,
  ⟨116,11,[-1],235⟩,
  ⟨116,12,[-1],236⟩,
  ⟨116,13,[-1],262⟩,
  ⟨116,14,[-1],235⟩,
  ⟨116,15,[-1],235⟩,
  ⟨116,16,[-1],543⟩,
  ⟨116,17,[-1],561⟩,
  ⟨116,18,[-1],542⟩,
  ⟨116,19,[-1],542⟩,
  ⟨116,20,[-1],543⟩,
  ⟨116,21,[-1],561⟩,
  ⟨116,22,[-1],542⟩,
  ⟨116,23,[-1],542⟩,
  ⟨116,24,[-1],956⟩,
  ⟨116,25,[-1],974⟩,
  ⟨116,26,[-1],955⟩,
  ⟨116,27,[-1],955⟩,
  ⟨116,28,[-1],956⟩,
  ⟨116,29,[-1],974⟩,
  ⟨116,30,[-1],955⟩,
  ⟨116,31,[-1],955⟩,
  ⟨116,32,[-1],236⟩,
  ⟨116,33,[-1],262⟩,
  ⟨116,34,[-1],241⟩,
  ⟨116,35,[-1],268⟩,
  ⟨116,36,[-1],236⟩,
  ⟨116,37,[-1],262⟩,
  ⟨116,38,[-1],241⟩,
  ⟨116,39,[-1],268⟩,
  ⟨116,40,[-1],236⟩,
  ⟨116,41,[-1],262⟩,
  ⟨116,42,[-1],241⟩,
  ⟨116,43,[-1],255⟩,
  ⟨116,44,[-1],236⟩,
  ⟨116,45,[-1],262⟩,
  ⟨116,46,[-1],241⟩,
  ⟨116,47,[-1],255⟩,
  ⟨116,48,[-1],543⟩,
  ⟨116,49,[-1],561⟩,
  ⟨116,50,[-1],547⟩,
  ⟨116,51,[-1],557⟩,
  ⟨116,52,[-1],543⟩,
  ⟨116,53,[-1],561⟩,
  ⟨116,54,[-1],547⟩,
  ⟨116,55,[-1],557⟩,
  ⟨116,56,[-1],956⟩,
  ⟨116,57,[-1],974⟩,
  ⟨116,58,[-1],960⟩,
  ⟨116,59,[-1],971⟩,
  ⟨116,60,[-1],956⟩,
  ⟨116,61,[-1],974⟩,
  ⟨116,62,[-1],960⟩,
  ⟨116,63,[-1],971⟩
]

private theorem goal_subset_115 : ∀ r ∈ goalRecords_115, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_115 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 116)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 116) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_115, r.goal = 116 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_115, r.goal = 116 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_115 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 116)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 116) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 116 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 116 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_115 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_115 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_115 r hr, hg, hb, hp⟩

private def goalRecords_116 : List MiddleCertRecord := [

]

private theorem goal_subset_116 : ∀ r ∈ goalRecords_116, r ∈ selectedRecords := by
  decide +kernel

private theorem goal_cover_116 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 117)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 117) j).2 = .automatic ∨
        (∃ r ∈ goalRecords_116, r.goal = 117 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ goalRecords_116, r.goal = 117 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_116 : ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 117)).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData 117) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = 117 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = 117 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rcases goal_cover_116 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ⟨r, goal_subset_116 r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, ?_⟩)
    intro k hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, goal_subset_116 r hr, hg, hb, hp⟩

private theorem coverage :
    ∀ i ∈ selectedGoals,
      ∀ j ∈ List.range (middleCertGoalBranches middleCertData (middleCertGoal middleCertData (i+1))).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData (i+1)) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (6 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 6)).length,
          ∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents)  := by
  simp only [selectedGoals, List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨cover_97, cover_98, cover_99, cover_100, cover_101, cover_102, cover_103, cover_104, cover_105, cover_106, cover_107, cover_108, cover_109, cover_110, cover_111, cover_112, cover_113, cover_114, cover_115, cover_116, List.forall_mem_nil _⟩

end FastFamily6

open FastFamily6

theorem solution : middleCertFamilyValid middleCertData 6 := by
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
