-- Prove2me | solution 1 for Freiman.section14_s0008_records_1184_1216
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:19:45.330347+00:00
-- url     : https://prove2.me/submissions/02c5eda0-d3ab-4a5b-950e-26df40ae42c6

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
namespace Section14Records_8_1184_1216
private theorem valid1184 : RecordDataValid section14Catalog 8 (⟨167,(10),[4,8,12,16],[10],1287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1287,[4,8,9,12,16],1291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1185 : RecordDataValid section14Catalog 8 (⟨167,(11),[4,8,12,16],[10],1288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1288,[4,8,9,12,16],1292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1186 : RecordDataValid section14Catalog 8 (⟨167,(12),[4,8,12,16],[10],1290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1290,[4,8,9,12,16],1294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1187 : RecordDataValid section14Catalog 8 (⟨167,(13),[4,8,12,16],[10],1286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1286,[4,8,9,12,16],1290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1188 : RecordDataValid section14Catalog 8 (⟨167,(14),[4,8,12,16],[10],1287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1287,[4,8,9,12,16],1291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1189 : RecordDataValid section14Catalog 8 (⟨167,(15),[4,8,12,16],[10],1288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1288,[4,8,9,12,16],1292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1190 : RecordDataValid section14Catalog 8 (⟨171,(0),[3,4,8,12,15,16],[10],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1191 : RecordDataValid section14Catalog 8 (⟨171,(1),[3,4,8,12,15,16],[10],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1192 : RecordDataValid section14Catalog 8 (⟨171,(2),[3,4,8,12,15,16],[10],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1193 : RecordDataValid section14Catalog 8 (⟨171,(3),[3,4,8,12,15,16],[10],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1194 : RecordDataValid section14Catalog 8 (⟨172,(0),[4,8,12,16],[10],1291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1291,[4,8,9,12,16],1295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1195 : RecordDataValid section14Catalog 8 (⟨172,(1),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1196 : RecordDataValid section14Catalog 8 (⟨172,(2),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1197 : RecordDataValid section14Catalog 8 (⟨172,(3),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1198 : RecordDataValid section14Catalog 8 (⟨172,(4),[4,8,12,16],[10],1295⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1295,[4,8,9,12,16],1299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1199 : RecordDataValid section14Catalog 8 (⟨172,(5),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1200 : RecordDataValid section14Catalog 8 (⟨172,(6),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1201 : RecordDataValid section14Catalog 8 (⟨172,(7),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1202 : RecordDataValid section14Catalog 8 (⟨172,(8),[4,8,12,16],[10],1291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1291,[4,8,9,12,16],1295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1203 : RecordDataValid section14Catalog 8 (⟨172,(9),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1204 : RecordDataValid section14Catalog 8 (⟨172,(10),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1205 : RecordDataValid section14Catalog 8 (⟨172,(11),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1206 : RecordDataValid section14Catalog 8 (⟨172,(12),[4,8,12,16],[10],1296⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1296,[4,8,9,12,16],1300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1207 : RecordDataValid section14Catalog 8 (⟨172,(13),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1208 : RecordDataValid section14Catalog 8 (⟨172,(14),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1209 : RecordDataValid section14Catalog 8 (⟨172,(15),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1210 : RecordDataValid section14Catalog 8 (⟨175,(0),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1211 : RecordDataValid section14Catalog 8 (⟨175,(1),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1212 : RecordDataValid section14Catalog 8 (⟨175,(2),[3,4,8,12,15,16],[10],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1213 : RecordDataValid section14Catalog 8 (⟨175,(3),[3,4,8,12,15,16],[10],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1214 : RecordDataValid section14Catalog 8 (⟨175,(4),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1215 : RecordDataValid section14Catalog 8 (⟨175,(5),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1184).take 32 = [⟨167,(10),[4,8,12,16],[10],1287⟩,⟨167,(11),[4,8,12,16],[10],1288⟩,⟨167,(12),[4,8,12,16],[10],1290⟩,⟨167,(13),[4,8,12,16],[10],1286⟩,⟨167,(14),[4,8,12,16],[10],1287⟩,⟨167,(15),[4,8,12,16],[10],1288⟩,⟨171,(0),[3,4,8,12,15,16],[10],650⟩,⟨171,(1),[3,4,8,12,15,16],[10],651⟩,⟨171,(2),[3,4,8,12,15,16],[10],652⟩,⟨171,(3),[3,4,8,12,15,16],[10],653⟩,⟨172,(0),[4,8,12,16],[10],1291⟩,⟨172,(1),[4,8,12,16],[10],1292⟩,⟨172,(2),[4,8,12,16],[10],1293⟩,⟨172,(3),[4,8,12,16],[10],1294⟩,⟨172,(4),[4,8,12,16],[10],1295⟩,⟨172,(5),[4,8,12,16],[10],1292⟩,⟨172,(6),[4,8,12,16],[10],1293⟩,⟨172,(7),[4,8,12,16],[10],1294⟩,⟨172,(8),[4,8,12,16],[10],1291⟩,⟨172,(9),[4,8,12,16],[10],1292⟩,⟨172,(10),[4,8,12,16],[10],1293⟩,⟨172,(11),[4,8,12,16],[10],1294⟩,⟨172,(12),[4,8,12,16],[10],1296⟩,⟨172,(13),[4,8,12,16],[10],1292⟩,⟨172,(14),[4,8,12,16],[10],1293⟩,⟨172,(15),[4,8,12,16],[10],1294⟩,⟨175,(0),[3,4,8,12,15,16],[10],654⟩,⟨175,(1),[3,4,8,12,15,16],[10],655⟩,⟨175,(2),[3,4,8,12,15,16],[10],656⟩,⟨175,(3),[3,4,8,12,15,16],[10],657⟩,⟨175,(4),[3,4,8,12,15,16],[10],654⟩,⟨175,(5),[3,4,8,12,15,16],[10],655⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1184
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1185
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1186
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1187
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1188
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1189
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1190
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1191
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1192
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1193
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1194
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1195
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1196
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1197
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1198
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1199
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1200
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1201
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1202
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1203
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1204
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1205
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1206
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1207
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1208
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1209
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1210
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1211
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1212
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1213
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1214
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1215
end Section14Records_8_1184_1216

#print axioms solution
