-- Prove2me | solution 1 for Freiman.section14_s0011_records_1056_1120
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:48:19.62807+00:00
-- url     : https://prove2.me/submissions/59267525-bfff-495c-a860-4cd893c50e8c

import Definitions.Def_Freiman_section14Data
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

open Freiman
set_option synthInstance.maxSize 100000
set_option maxRecDepth 100000
namespace M7Section14Sep18
instance (r : CertRectangle) : Decidable (certRectangleValid r) := by
  unfold certRectangleValid
  infer_instance
instance (t : CertThreshold) : Decidable (certThresholdDataValid t) := by
  unfold certThresholdDataValid
  infer_instance
instance (z : CertField) (q : ℚ) : Decidable (certCoefficientBoundValid z q) := by
  unfold certCoefficientBoundValid
  infer_instance
instance (w : CertWitness) : Decidable (certWitnessValid w) := by
  unfold certWitnessValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (caseId : ℕ)
    (gs : ℕ × Section14Spec) : Decidable (section14SpecValid C S caseId gs) := by
  unfold section14SpecValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (p : Section14Plan) :
    Decidable (section14PlanValid C S p) := by
  unfold section14PlanValid
  infer_instance
instance (outer inner : CertRectangle) : Decidable (section14RectangleContains outer inner) := by
  unfold section14RectangleContains
  infer_instance
instance (C : Section14Catalog) (si : ℕ) (r : Section14Record) :
    Decidable (section14RecordValid C si r) := by
  unfold section14RecordValid
  infer_instance
instance (C : Section14Catalog) (si parent goal : ℕ) (branch : ℤ) :
    Decidable (section14Recorded C si parent goal branch) := by
  unfold section14Recorded
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14Coverage C si) := by
  unfold section14Coverage
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14StateValid C si) := by
  unfold section14StateValid
  infer_instance
end M7Section14Sep18

open Freiman
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000
set_option Elab.async false
namespace M7Section14Sep18

def RecordDataValid (C : Section14Catalog) (si : ℕ) (r : Section14Record) : Prop :=
  let S := section14State C si
  let p := section14Proof C r.proofId
  0 < r.goal ∧ r.goal ≤ C.goals.length ∧ 0 < r.proofId ∧ r.proofId ≤ C.proofs.length ∧
  (section14Branch C (section14Goal C r.goal) r.branch).2 ≠ .automatic ∧
  (∀ b ∈ section14Parents C S, b.branch ∈ r.parents →
    section14Bound C p.lowerBound ∈ section14RecordConditions C r b ∧
    section14Bound C p.upperBound ∈ section14RecordConditions C r b) ∧
  ∃ a ∈ C.assignments, a.proofId = r.proofId ∧ si ∈ a.states ∧
    0 < a.witnessId ∧ a.witnessId ≤ C.witnesses.length ∧
    let w := section14Witness C a.witnessId
    w.firstThreshold = p.lowerBound.threshold ∧ w.secondThreshold = p.upperBound.threshold ∧
    section14RectangleContains w.rectangle S.rectangle

instance (C : Section14Catalog) (si : ℕ) (r : Section14Record) :
    Decidable (RecordDataValid C si r) := by
  unfold RecordDataValid
  infer_instance

theorem recordValid_of_data (C : Section14Catalog) (si : ℕ) (r : Section14Record)
    (hnum : ∀ a ∈ C.assignments, certWitnessValid
      (section14PairWitness C (section14Proof C a.proofId) (section14Witness C a.witnessId)))
    (h : RecordDataValid C si r) : section14RecordValid C si r := by
  rcases h with ⟨hg0,hg1,hp0,hp1,hbranch,hconditions,a,ha,hp,hs,hw0,hw1,hl,hu,hrect⟩
  have hv := hnum a ha
  rw [hp] at hv
  exact ⟨hg0,hg1,hp0,hp1,hbranch,hconditions,a,ha,hp,hs,hw0,hw1,hl,hu,hrect,hv⟩

theorem recordValid_all_of_data (C : Section14Catalog) (si : ℕ)
    (hnum : ∀ a ∈ C.assignments, certWitnessValid
      (section14PairWitness C (section14Proof C a.proofId) (section14Witness C a.witnessId)))
    (h : ∀ r ∈ C.records, si ∈ r.states → RecordDataValid C si r) :
    ∀ r ∈ C.records, si ∈ r.states → section14RecordValid C si r := by
  intro r hr hs
  exact recordValid_of_data C si r hnum (h r hr hs)
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_11_1056_1120
private theorem valid1056 : RecordDataValid section14Catalog 11 (⟨436,(9),[11],[2],1126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1126,[3,5,7,8,9,11,12,15],1130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1057 : RecordDataValid section14Catalog 11 (⟨438,(0),[11],[2],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1058 : RecordDataValid section14Catalog 11 (⟨438,(1),[11],[2],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1059 : RecordDataValid section14Catalog 11 (⟨438,(2),[11],[2],1128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1128,[3,7,11,15],1132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1060 : RecordDataValid section14Catalog 11 (⟨438,(3),[11],[2],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1061 : RecordDataValid section14Catalog 11 (⟨438,(4),[11],[2],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1062 : RecordDataValid section14Catalog 11 (⟨438,(5),[11],[2],1131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1131,[3,7,11,15],1135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1063 : RecordDataValid section14Catalog 11 (⟨438,(6),[11],[2],1131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1131,[3,7,11,15],1135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1064 : RecordDataValid section14Catalog 11 (⟨438,(7),[11],[2],1128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1128,[3,7,11,15],1132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1065 : RecordDataValid section14Catalog 11 (⟨438,(8),[11],[2],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1066 : RecordDataValid section14Catalog 11 (⟨438,(9),[11],[2],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1067 : RecordDataValid section14Catalog 11 (⟨438,(10),[11],[2],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1068 : RecordDataValid section14Catalog 11 (⟨438,(11),[11],[2],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1069 : RecordDataValid section14Catalog 11 (⟨438,(12),[11],[2],1128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1128,[3,7,11,15],1132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1070 : RecordDataValid section14Catalog 11 (⟨438,(13),[11],[2],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1071 : RecordDataValid section14Catalog 11 (⟨438,(14),[11],[2],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1072 : RecordDataValid section14Catalog 11 (⟨438,(15),[11],[2],1132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1132,[3,7,11,15],1136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1073 : RecordDataValid section14Catalog 11 (⟨438,(16),[11],[2],1132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1132,[3,7,11,15],1136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1074 : RecordDataValid section14Catalog 11 (⟨438,(17),[11],[2],1128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1128,[3,7,11,15],1132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1075 : RecordDataValid section14Catalog 11 (⟨438,(18),[11],[2],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1076 : RecordDataValid section14Catalog 11 (⟨438,(19),[11],[2],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1077 : RecordDataValid section14Catalog 11 (⟨438,(20),[11],[2],1133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1133,[3,7,11,15],1137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1078 : RecordDataValid section14Catalog 11 (⟨438,(21),[11],[2],1133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1133,[3,7,11,15],1137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1079 : RecordDataValid section14Catalog 11 (⟨438,(22),[11],[2],1133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1133,[3,7,11,15],1137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1080 : RecordDataValid section14Catalog 11 (⟨438,(23),[11],[2],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1081 : RecordDataValid section14Catalog 11 (⟨438,(24),[11],[2],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1082 : RecordDataValid section14Catalog 11 (⟨441,(0),[11],[2],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1083 : RecordDataValid section14Catalog 11 (⟨441,(1),[11],[2],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1084 : RecordDataValid section14Catalog 11 (⟨441,(2),[11],[2],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1085 : RecordDataValid section14Catalog 11 (⟨441,(3),[11],[2],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1086 : RecordDataValid section14Catalog 11 (⟨441,(4),[11],[2],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1087 : RecordDataValid section14Catalog 11 (⟨441,(5),[11],[2],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1088 : RecordDataValid section14Catalog 11 (⟨441,(6),[11],[2],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1089 : RecordDataValid section14Catalog 11 (⟨441,(7),[11],[2],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1090 : RecordDataValid section14Catalog 11 (⟨441,(8),[11],[2],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1091 : RecordDataValid section14Catalog 11 (⟨441,(9),[11],[2],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1092 : RecordDataValid section14Catalog 11 (⟨441,(10),[11],[2],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1093 : RecordDataValid section14Catalog 11 (⟨441,(11),[11],[2],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1094 : RecordDataValid section14Catalog 11 (⟨441,(12),[11],[2],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1095 : RecordDataValid section14Catalog 11 (⟨441,(13),[11],[2],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1096 : RecordDataValid section14Catalog 11 (⟨441,(14),[11],[2],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1097 : RecordDataValid section14Catalog 11 (⟨441,(15),[11],[2],1140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1140,[3,5,7,8,9,11,12,15],1144⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1098 : RecordDataValid section14Catalog 11 (⟨441,(16),[11],[2],1141⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1141,[3,5,7,8,9,11,12,15],1145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1099 : RecordDataValid section14Catalog 11 (⟨441,(17),[11],[2],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1100 : RecordDataValid section14Catalog 11 (⟨441,(18),[11],[2],1143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1143,[3,5,7,8,9,11,12,15],1147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1101 : RecordDataValid section14Catalog 11 (⟨441,(19),[11],[2],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1102 : RecordDataValid section14Catalog 11 (⟨441,(20),[11],[2],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1103 : RecordDataValid section14Catalog 11 (⟨441,(21),[11],[2],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1104 : RecordDataValid section14Catalog 11 (⟨441,(22),[11],[2],1144⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1144,[3,5,7,8,9,11,12,15],1148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1105 : RecordDataValid section14Catalog 11 (⟨441,(23),[11],[2],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1106 : RecordDataValid section14Catalog 11 (⟨441,(24),[11],[2],1144⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1144,[3,5,7,8,9,11,12,15],1148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1107 : RecordDataValid section14Catalog 11 (⟨443,(0),[11],[2],1145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1145,[3,7,11,15],1149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1108 : RecordDataValid section14Catalog 11 (⟨443,(1),[11],[2],1145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1145,[3,7,11,15],1149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1109 : RecordDataValid section14Catalog 11 (⟨443,(2),[11],[2],1146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1146,[3,7,11,15],1150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1110 : RecordDataValid section14Catalog 11 (⟨443,(3),[11],[2],1147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1147,[3,7,11,15],1151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1111 : RecordDataValid section14Catalog 11 (⟨443,(4),[11],[2],1148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1148,[3,7,11,15],1152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1112 : RecordDataValid section14Catalog 11 (⟨443,(5),[11],[2],1149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1149,[3,7,11,15],1153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1113 : RecordDataValid section14Catalog 11 (⟨443,(6),[11],[2],1149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1149,[3,7,11,15],1153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1114 : RecordDataValid section14Catalog 11 (⟨443,(7),[11],[2],1146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1146,[3,7,11,15],1150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1115 : RecordDataValid section14Catalog 11 (⟨443,(8),[11],[2],1147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1147,[3,7,11,15],1151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1116 : RecordDataValid section14Catalog 11 (⟨443,(9),[11],[2],1148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1148,[3,7,11,15],1152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1117 : RecordDataValid section14Catalog 11 (⟨443,(10),[11],[2],1145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1145,[3,7,11,15],1149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1118 : RecordDataValid section14Catalog 11 (⟨443,(11),[11],[2],1145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1145,[3,7,11,15],1149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1119 : RecordDataValid section14Catalog 11 (⟨443,(12),[11],[2],1146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1146,[3,7,11,15],1150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1056).take 64, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 1056).take 64 = [⟨436,(9),[11],[2],1126⟩,⟨438,(0),[11],[2],1127⟩,⟨438,(1),[11],[2],1127⟩,⟨438,(2),[11],[2],1128⟩,⟨438,(3),[11],[2],1129⟩,⟨438,(4),[11],[2],1130⟩,⟨438,(5),[11],[2],1131⟩,⟨438,(6),[11],[2],1131⟩,⟨438,(7),[11],[2],1128⟩,⟨438,(8),[11],[2],1129⟩,⟨438,(9),[11],[2],1130⟩,⟨438,(10),[11],[2],1127⟩,⟨438,(11),[11],[2],1127⟩,⟨438,(12),[11],[2],1128⟩,⟨438,(13),[11],[2],1129⟩,⟨438,(14),[11],[2],1130⟩,⟨438,(15),[11],[2],1132⟩,⟨438,(16),[11],[2],1132⟩,⟨438,(17),[11],[2],1128⟩,⟨438,(18),[11],[2],1129⟩,⟨438,(19),[11],[2],1130⟩,⟨438,(20),[11],[2],1133⟩,⟨438,(21),[11],[2],1133⟩,⟨438,(22),[11],[2],1133⟩,⟨438,(23),[11],[2],1129⟩,⟨438,(24),[11],[2],1130⟩,⟨441,(0),[11],[2],1134⟩,⟨441,(1),[11],[2],1135⟩,⟨441,(2),[11],[2],1136⟩,⟨441,(3),[11],[2],1136⟩,⟨441,(4),[11],[2],1136⟩,⟨441,(5),[11],[2],1134⟩,⟨441,(6),[11],[2],1135⟩,⟨441,(7),[11],[2],1137⟩,⟨441,(8),[11],[2],1138⟩,⟨441,(9),[11],[2],1137⟩,⟨441,(10),[11],[2],1134⟩,⟨441,(11),[11],[2],1135⟩,⟨441,(12),[11],[2],1139⟩,⟨441,(13),[11],[2],1138⟩,⟨441,(14),[11],[2],1139⟩,⟨441,(15),[11],[2],1140⟩,⟨441,(16),[11],[2],1141⟩,⟨441,(17),[11],[2],1142⟩,⟨441,(18),[11],[2],1143⟩,⟨441,(19),[11],[2],1142⟩,⟨441,(20),[11],[2],1134⟩,⟨441,(21),[11],[2],1135⟩,⟨441,(22),[11],[2],1144⟩,⟨441,(23),[11],[2],1138⟩,⟨441,(24),[11],[2],1144⟩,⟨443,(0),[11],[2],1145⟩,⟨443,(1),[11],[2],1145⟩,⟨443,(2),[11],[2],1146⟩,⟨443,(3),[11],[2],1147⟩,⟨443,(4),[11],[2],1148⟩,⟨443,(5),[11],[2],1149⟩,⟨443,(6),[11],[2],1149⟩,⟨443,(7),[11],[2],1146⟩,⟨443,(8),[11],[2],1147⟩,⟨443,(9),[11],[2],1148⟩,⟨443,(10),[11],[2],1145⟩,⟨443,(11),[11],[2],1145⟩,⟨443,(12),[11],[2],1146⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1056
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1057
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1058
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1059
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1060
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1061
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1062
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1063
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1064
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1065
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1066
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1067
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1068
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1069
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1070
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1071
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1072
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1073
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1074
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1075
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1076
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1077
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1078
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1079
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1080
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1081
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1082
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1083
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1084
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1085
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1086
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1087
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1088
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1089
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1090
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1091
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1092
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1093
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1094
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1095
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1096
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1097
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1098
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1099
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1100
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1101
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1102
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1103
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1104
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1105
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1106
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1107
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1108
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1109
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1110
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1111
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1112
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1113
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1114
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1115
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1116
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1117
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1118
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1119
end Section14Records_11_1056_1120

#print axioms solution
