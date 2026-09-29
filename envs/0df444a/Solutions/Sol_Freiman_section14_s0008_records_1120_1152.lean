-- Prove2me | solution 1 for Freiman.section14_s0008_records_1120_1152
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:17:22.145981+00:00
-- url     : https://prove2.me/submissions/b1b37a89-119d-4ce0-bd3a-c1af5ea65f49

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
namespace Section14Records_8_1120_1152
private theorem valid1120 : RecordDataValid section14Catalog 8 (⟨157,(19),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1121 : RecordDataValid section14Catalog 8 (⟨157,(20),[3,4,7,8,15,16],[10],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1122 : RecordDataValid section14Catalog 8 (⟨157,(21),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1123 : RecordDataValid section14Catalog 8 (⟨157,(22),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1124 : RecordDataValid section14Catalog 8 (⟨157,(23),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1125 : RecordDataValid section14Catalog 8 (⟨157,(24),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1126 : RecordDataValid section14Catalog 8 (⟨160,(0),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1127 : RecordDataValid section14Catalog 8 (⟨160,(1),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1128 : RecordDataValid section14Catalog 8 (⟨160,(2),[3,4,8,12,15,16],[10],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1129 : RecordDataValid section14Catalog 8 (⟨160,(3),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1130 : RecordDataValid section14Catalog 8 (⟨160,(4),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1131 : RecordDataValid section14Catalog 8 (⟨160,(5),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1132 : RecordDataValid section14Catalog 8 (⟨160,(6),[3,4,8,12,15,16],[10],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1133 : RecordDataValid section14Catalog 8 (⟨160,(7),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1134 : RecordDataValid section14Catalog 8 (⟨160,(8),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1135 : RecordDataValid section14Catalog 8 (⟨160,(9),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1136 : RecordDataValid section14Catalog 8 (⟨160,(10),[3,4,8,12,15,16],[10],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1137 : RecordDataValid section14Catalog 8 (⟨160,(11),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1138 : RecordDataValid section14Catalog 8 (⟨160,(12),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1139 : RecordDataValid section14Catalog 8 (⟨160,(13),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1140 : RecordDataValid section14Catalog 8 (⟨160,(14),[3,4,8,12,15,16],[10],643⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨643,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],644⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1141 : RecordDataValid section14Catalog 8 (⟨160,(15),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1142 : RecordDataValid section14Catalog 8 (⟨163,(0),[4,8,12,16],[10],1279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1279,[4,8,9,12,16],1283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1143 : RecordDataValid section14Catalog 8 (⟨163,(1),[4,8,12,16],[10],1280⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1280,[4,8,9,12,16],1284⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1144 : RecordDataValid section14Catalog 8 (⟨163,(2),[4,8,12,16],[10],1279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1279,[4,8,9,12,16],1283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1145 : RecordDataValid section14Catalog 8 (⟨163,(3),[4,8,12,16],[10],1281⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1281,[4,8,9,12,16],1285⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1146 : RecordDataValid section14Catalog 8 (⟨163,(4),[4,8,12,16],[10],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1147 : RecordDataValid section14Catalog 8 (⟨163,(5),[4,8,12,16],[10],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1148 : RecordDataValid section14Catalog 8 (⟨163,(6),[4,8,12,16],[10],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1149 : RecordDataValid section14Catalog 8 (⟨163,(7),[4,8,12,16],[10],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1150 : RecordDataValid section14Catalog 8 (⟨163,(8),[4,8,12,16],[10],1283⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1283,[4,8,9,12,16],1287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1151 : RecordDataValid section14Catalog 8 (⟨163,(9),[4,8,12,16],[10],1283⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1283,[4,8,9,12,16],1287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1120).take 32 = [⟨157,(19),[4,8,16],[10],1277⟩,⟨157,(20),[3,4,7,8,15,16],[10],24⟩,⟨157,(21),[4,8,16],[10],1278⟩,⟨157,(22),[4,8,16],[10],1278⟩,⟨157,(23),[4,8,16],[10],1278⟩,⟨157,(24),[4,8,16],[10],1278⟩,⟨160,(0),[3,4,8,12,15,16],[10],638⟩,⟨160,(1),[3,4,8,12,15,16],[10],639⟩,⟨160,(2),[3,4,8,12,15,16],[10],640⟩,⟨160,(3),[3,4,8,12,15,16],[10],641⟩,⟨160,(4),[3,4,8,12,15,16],[10],638⟩,⟨160,(5),[3,4,8,12,15,16],[10],639⟩,⟨160,(6),[3,4,8,12,15,16],[10],642⟩,⟨160,(7),[3,4,8,12,15,16],[10],641⟩,⟨160,(8),[3,4,8,12,15,16],[10],638⟩,⟨160,(9),[3,4,8,12,15,16],[10],639⟩,⟨160,(10),[3,4,8,12,15,16],[10],640⟩,⟨160,(11),[3,4,8,12,15,16],[10],641⟩,⟨160,(12),[3,4,8,12,15,16],[10],638⟩,⟨160,(13),[3,4,8,12,15,16],[10],639⟩,⟨160,(14),[3,4,8,12,15,16],[10],643⟩,⟨160,(15),[3,4,8,12,15,16],[10],641⟩,⟨163,(0),[4,8,12,16],[10],1279⟩,⟨163,(1),[4,8,12,16],[10],1280⟩,⟨163,(2),[4,8,12,16],[10],1279⟩,⟨163,(3),[4,8,12,16],[10],1281⟩,⟨163,(4),[4,8,12,16],[10],1282⟩,⟨163,(5),[4,8,12,16],[10],1282⟩,⟨163,(6),[4,8,12,16],[10],1282⟩,⟨163,(7),[4,8,12,16],[10],1282⟩,⟨163,(8),[4,8,12,16],[10],1283⟩,⟨163,(9),[4,8,12,16],[10],1283⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1120
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1121
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1122
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1123
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1124
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1125
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1126
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1127
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1128
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1129
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1130
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1131
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1132
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1133
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1134
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1135
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1136
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1137
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1138
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1139
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1140
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1141
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1142
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1143
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1144
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1145
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1146
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1147
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1148
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1149
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1150
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1151
end Section14Records_8_1120_1152

#print axioms solution
