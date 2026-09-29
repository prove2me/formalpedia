-- Prove2me | solution 1 for Freiman.section14_s0008_records_1088_1120
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:16:15.109983+00:00
-- url     : https://prove2.me/submissions/17e27dc8-23ba-4ce8-b9f6-617fb973302e

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
namespace Section14Records_8_1088_1120
private theorem valid1088 : RecordDataValid section14Catalog 8 (⟨150,(22),[4,8,12],[10],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1089 : RecordDataValid section14Catalog 8 (⟨150,(23),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1090 : RecordDataValid section14Catalog 8 (⟨150,(24),[4,8,12],[10],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1091 : RecordDataValid section14Catalog 8 (⟨153,(-1),[2,4,6,8,10,12,14,16],[0,4],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1092 : RecordDataValid section14Catalog 8 (⟨153,(-1),[3,4,7,8,12,15,16],[5],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1093 : RecordDataValid section14Catalog 8 (⟨153,(-1),[4,8,10,12,16],[8,12],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1094 : RecordDataValid section14Catalog 8 (⟨153,(-1),[4,8,11,12,16],[1],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1095 : RecordDataValid section14Catalog 8 (⟨153,(-1),[4,8,12,16],[9,13],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1096 : RecordDataValid section14Catalog 8 (⟨153,(-1),[4,8,12,16],[2],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1097 : RecordDataValid section14Catalog 8 (⟨153,(-1),[4,8,12,16],[7,11,15],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1098 : RecordDataValid section14Catalog 8 (⟨153,(-1),[4,8,12,16],[6],637⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨637,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],638⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1099 : RecordDataValid section14Catalog 8 (⟨153,(-1),[4,8,12,16],[14],879⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨879,[1,2,4,5,6,8,9,10,12,13,14,16],881⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1100 : RecordDataValid section14Catalog 8 (⟨153,(-1),[8,12],[3],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1101 : RecordDataValid section14Catalog 8 (⟨157,(0),[3,4,7,8,15,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1102 : RecordDataValid section14Catalog 8 (⟨157,(1),[4,8,16],[10],1272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1272,[4,8,16],1276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1103 : RecordDataValid section14Catalog 8 (⟨157,(2),[4,8,16],[10],1273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1273,[4,8,16],1277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1104 : RecordDataValid section14Catalog 8 (⟨157,(3),[4,8,16],[10],1274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1274,[4,8,16],1278⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1105 : RecordDataValid section14Catalog 8 (⟨157,(4),[4,8,16],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1106 : RecordDataValid section14Catalog 8 (⟨157,(5),[3,4,7,8,15,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1107 : RecordDataValid section14Catalog 8 (⟨157,(6),[4,8,16],[10],1272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1272,[4,8,16],1276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1108 : RecordDataValid section14Catalog 8 (⟨157,(7),[4,8,16],[10],1273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1273,[4,8,16],1277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1109 : RecordDataValid section14Catalog 8 (⟨157,(8),[4,8,16],[10],1274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1274,[4,8,16],1278⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1110 : RecordDataValid section14Catalog 8 (⟨157,(9),[4,8,16],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1111 : RecordDataValid section14Catalog 8 (⟨157,(10),[3,4,7,8,15,16],[10],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1112 : RecordDataValid section14Catalog 8 (⟨157,(11),[4,8,16],[10],1276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1276,[4,8,16],1280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1113 : RecordDataValid section14Catalog 8 (⟨157,(12),[4,8,16],[10],1276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1276,[4,8,16],1280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1114 : RecordDataValid section14Catalog 8 (⟨157,(13),[4,8,16],[10],1276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1276,[4,8,16],1280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1115 : RecordDataValid section14Catalog 8 (⟨157,(14),[4,8,16],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1116 : RecordDataValid section14Catalog 8 (⟨157,(15),[3,4,7,8,15,16],[10],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1117 : RecordDataValid section14Catalog 8 (⟨157,(16),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1118 : RecordDataValid section14Catalog 8 (⟨157,(17),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1119 : RecordDataValid section14Catalog 8 (⟨157,(18),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1088).take 32 = [⟨150,(22),[4,8,12],[10],287⟩,⟨150,(23),[4,8,12],[10],101⟩,⟨150,(24),[4,8,12],[10],287⟩,⟨153,(-1),[2,4,6,8,10,12,14,16],[0,4],632⟩,⟨153,(-1),[3,4,7,8,12,15,16],[5],633⟩,⟨153,(-1),[4,8,10,12,16],[8,12],632⟩,⟨153,(-1),[4,8,11,12,16],[1],633⟩,⟨153,(-1),[4,8,12,16],[9,13],633⟩,⟨153,(-1),[4,8,12,16],[2],634⟩,⟨153,(-1),[4,8,12,16],[7,11,15],636⟩,⟨153,(-1),[4,8,12,16],[6],637⟩,⟨153,(-1),[4,8,12,16],[14],879⟩,⟨153,(-1),[8,12],[3],636⟩,⟨157,(0),[3,4,7,8,15,16],[10],10⟩,⟨157,(1),[4,8,16],[10],1272⟩,⟨157,(2),[4,8,16],[10],1273⟩,⟨157,(3),[4,8,16],[10],1274⟩,⟨157,(4),[4,8,16],[10],1275⟩,⟨157,(5),[3,4,7,8,15,16],[10],10⟩,⟨157,(6),[4,8,16],[10],1272⟩,⟨157,(7),[4,8,16],[10],1273⟩,⟨157,(8),[4,8,16],[10],1274⟩,⟨157,(9),[4,8,16],[10],1275⟩,⟨157,(10),[3,4,7,8,15,16],[10],18⟩,⟨157,(11),[4,8,16],[10],1276⟩,⟨157,(12),[4,8,16],[10],1276⟩,⟨157,(13),[4,8,16],[10],1276⟩,⟨157,(14),[4,8,16],[10],1275⟩,⟨157,(15),[3,4,7,8,15,16],[10],21⟩,⟨157,(16),[4,8,16],[10],1277⟩,⟨157,(17),[4,8,16],[10],1277⟩,⟨157,(18),[4,8,16],[10],1277⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1088
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1089
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1090
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1091
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1092
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1093
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1094
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1095
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1096
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1097
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1098
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1099
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1100
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1101
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1102
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1103
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1104
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1105
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1106
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1107
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1108
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1109
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1110
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1111
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1112
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1113
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1114
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1115
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1116
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1117
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1118
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1119
end Section14Records_8_1088_1120

#print axioms solution
