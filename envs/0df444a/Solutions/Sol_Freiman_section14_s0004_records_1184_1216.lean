-- Prove2me | solution 1 for Freiman.section14_s0004_records_1184_1216
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:32:47.142706+00:00
-- url     : https://prove2.me/submissions/492c4f71-1033-43b5-b9cd-397794be5033

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
namespace Section14Records_4_1184_1216
private theorem valid1184 : RecordDataValid section14Catalog 4 (⟨157,(24),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1185 : RecordDataValid section14Catalog 4 (⟨160,(0),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1186 : RecordDataValid section14Catalog 4 (⟨160,(1),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1187 : RecordDataValid section14Catalog 4 (⟨160,(2),[3,4,8,12,15,16],[10],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1188 : RecordDataValid section14Catalog 4 (⟨160,(3),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1189 : RecordDataValid section14Catalog 4 (⟨160,(4),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1190 : RecordDataValid section14Catalog 4 (⟨160,(5),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1191 : RecordDataValid section14Catalog 4 (⟨160,(6),[3,4,8,12,15,16],[10],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1192 : RecordDataValid section14Catalog 4 (⟨160,(7),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1193 : RecordDataValid section14Catalog 4 (⟨160,(8),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1194 : RecordDataValid section14Catalog 4 (⟨160,(9),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1195 : RecordDataValid section14Catalog 4 (⟨160,(10),[3,4,8,12,15,16],[10],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1196 : RecordDataValid section14Catalog 4 (⟨160,(11),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1197 : RecordDataValid section14Catalog 4 (⟨160,(12),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1198 : RecordDataValid section14Catalog 4 (⟨160,(13),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1199 : RecordDataValid section14Catalog 4 (⟨160,(14),[3,4,8,12,15,16],[10],643⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨643,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],644⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1200 : RecordDataValid section14Catalog 4 (⟨160,(15),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1201 : RecordDataValid section14Catalog 4 (⟨163,(0),[4,8,12,16],[10],1279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1279,[4,8,9,12,16],1283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1202 : RecordDataValid section14Catalog 4 (⟨163,(1),[4,8,12,16],[10],1280⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1280,[4,8,9,12,16],1284⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1203 : RecordDataValid section14Catalog 4 (⟨163,(2),[4,8,12,16],[10],1279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1279,[4,8,9,12,16],1283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1204 : RecordDataValid section14Catalog 4 (⟨163,(3),[4,8,12,16],[10],1281⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1281,[4,8,9,12,16],1285⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1205 : RecordDataValid section14Catalog 4 (⟨163,(4),[4,8,12,16],[10],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1206 : RecordDataValid section14Catalog 4 (⟨163,(5),[4,8,12,16],[10],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1207 : RecordDataValid section14Catalog 4 (⟨163,(6),[4,8,12,16],[10],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1208 : RecordDataValid section14Catalog 4 (⟨163,(7),[4,8,12,16],[10],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1209 : RecordDataValid section14Catalog 4 (⟨163,(8),[4,8,12,16],[10],1283⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1283,[4,8,9,12,16],1287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1210 : RecordDataValid section14Catalog 4 (⟨163,(9),[4,8,12,16],[10],1283⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1283,[4,8,9,12,16],1287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1211 : RecordDataValid section14Catalog 4 (⟨163,(10),[4,8,12,16],[10],1283⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1283,[4,8,9,12,16],1287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1212 : RecordDataValid section14Catalog 4 (⟨163,(11),[4,8,12,16],[10],1283⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1283,[4,8,9,12,16],1287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1213 : RecordDataValid section14Catalog 4 (⟨163,(12),[4,8,12,16],[10],1284⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1284,[4,8,9,12,16],1288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1214 : RecordDataValid section14Catalog 4 (⟨163,(13),[4,8,12,16],[10],1284⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1284,[4,8,9,12,16],1288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1215 : RecordDataValid section14Catalog 4 (⟨163,(14),[4,8,12,16],[10],1284⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1284,[4,8,9,12,16],1288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1184).take 32 = [⟨157,(24),[4,8,16],[10],1278⟩,⟨160,(0),[3,4,8,12,15,16],[10],638⟩,⟨160,(1),[3,4,8,12,15,16],[10],639⟩,⟨160,(2),[3,4,8,12,15,16],[10],640⟩,⟨160,(3),[3,4,8,12,15,16],[10],641⟩,⟨160,(4),[3,4,8,12,15,16],[10],638⟩,⟨160,(5),[3,4,8,12,15,16],[10],639⟩,⟨160,(6),[3,4,8,12,15,16],[10],642⟩,⟨160,(7),[3,4,8,12,15,16],[10],641⟩,⟨160,(8),[3,4,8,12,15,16],[10],638⟩,⟨160,(9),[3,4,8,12,15,16],[10],639⟩,⟨160,(10),[3,4,8,12,15,16],[10],640⟩,⟨160,(11),[3,4,8,12,15,16],[10],641⟩,⟨160,(12),[3,4,8,12,15,16],[10],638⟩,⟨160,(13),[3,4,8,12,15,16],[10],639⟩,⟨160,(14),[3,4,8,12,15,16],[10],643⟩,⟨160,(15),[3,4,8,12,15,16],[10],641⟩,⟨163,(0),[4,8,12,16],[10],1279⟩,⟨163,(1),[4,8,12,16],[10],1280⟩,⟨163,(2),[4,8,12,16],[10],1279⟩,⟨163,(3),[4,8,12,16],[10],1281⟩,⟨163,(4),[4,8,12,16],[10],1282⟩,⟨163,(5),[4,8,12,16],[10],1282⟩,⟨163,(6),[4,8,12,16],[10],1282⟩,⟨163,(7),[4,8,12,16],[10],1282⟩,⟨163,(8),[4,8,12,16],[10],1283⟩,⟨163,(9),[4,8,12,16],[10],1283⟩,⟨163,(10),[4,8,12,16],[10],1283⟩,⟨163,(11),[4,8,12,16],[10],1283⟩,⟨163,(12),[4,8,12,16],[10],1284⟩,⟨163,(13),[4,8,12,16],[10],1284⟩,⟨163,(14),[4,8,12,16],[10],1284⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1184
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1185
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1186
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1187
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1188
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1189
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1190
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1191
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1192
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1193
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1194
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1195
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1196
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1197
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1198
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1199
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1200
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1201
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1202
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1203
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1204
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1205
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1206
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1207
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1208
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1209
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1210
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1211
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1212
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1213
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1214
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1215
end Section14Records_4_1184_1216

#print axioms solution
