-- Prove2me | solution 1 for Freiman.section14_s0004_records_1248_1280
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:35:09.254444+00:00
-- url     : https://prove2.me/submissions/10ff0ac6-d793-4f5c-ac1b-478789f08c4c

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
namespace Section14Records_4_1248_1280
private theorem valid1248 : RecordDataValid section14Catalog 4 (⟨167,(15),[4,8,12,16],[10],1288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1288,[4,8,9,12,16],1292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1249 : RecordDataValid section14Catalog 4 (⟨171,(0),[3,4,8,12,15,16],[10],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1250 : RecordDataValid section14Catalog 4 (⟨171,(1),[3,4,8,12,15,16],[10],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1251 : RecordDataValid section14Catalog 4 (⟨171,(2),[3,4,8,12,15,16],[10],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1252 : RecordDataValid section14Catalog 4 (⟨171,(3),[3,4,8,12,15,16],[10],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1253 : RecordDataValid section14Catalog 4 (⟨172,(0),[4,8,12,16],[10],1291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1291,[4,8,9,12,16],1295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1254 : RecordDataValid section14Catalog 4 (⟨172,(1),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1255 : RecordDataValid section14Catalog 4 (⟨172,(2),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1256 : RecordDataValid section14Catalog 4 (⟨172,(3),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1257 : RecordDataValid section14Catalog 4 (⟨172,(4),[4,8,12,16],[10],1295⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1295,[4,8,9,12,16],1299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1258 : RecordDataValid section14Catalog 4 (⟨172,(5),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1259 : RecordDataValid section14Catalog 4 (⟨172,(6),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1260 : RecordDataValid section14Catalog 4 (⟨172,(7),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1261 : RecordDataValid section14Catalog 4 (⟨172,(8),[4,8,12,16],[10],1291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1291,[4,8,9,12,16],1295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1262 : RecordDataValid section14Catalog 4 (⟨172,(9),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1263 : RecordDataValid section14Catalog 4 (⟨172,(10),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1264 : RecordDataValid section14Catalog 4 (⟨172,(11),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1265 : RecordDataValid section14Catalog 4 (⟨172,(12),[4,8,12,16],[10],1296⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1296,[4,8,9,12,16],1300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1266 : RecordDataValid section14Catalog 4 (⟨172,(13),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1267 : RecordDataValid section14Catalog 4 (⟨172,(14),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1268 : RecordDataValid section14Catalog 4 (⟨172,(15),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1269 : RecordDataValid section14Catalog 4 (⟨175,(0),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1270 : RecordDataValid section14Catalog 4 (⟨175,(1),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1271 : RecordDataValid section14Catalog 4 (⟨175,(2),[3,4,8,12,15,16],[10],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1272 : RecordDataValid section14Catalog 4 (⟨175,(3),[3,4,8,12,15,16],[10],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1273 : RecordDataValid section14Catalog 4 (⟨175,(4),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1274 : RecordDataValid section14Catalog 4 (⟨175,(5),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1275 : RecordDataValid section14Catalog 4 (⟨175,(6),[3,4,8,12,15,16],[10],658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨658,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],659⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1276 : RecordDataValid section14Catalog 4 (⟨175,(7),[3,4,8,12,15,16],[10],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1277 : RecordDataValid section14Catalog 4 (⟨175,(8),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1278 : RecordDataValid section14Catalog 4 (⟨175,(9),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1279 : RecordDataValid section14Catalog 4 (⟨175,(10),[3,4,8,12,15,16],[10],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1248).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1248).take 32 = [⟨167,(15),[4,8,12,16],[10],1288⟩,⟨171,(0),[3,4,8,12,15,16],[10],650⟩,⟨171,(1),[3,4,8,12,15,16],[10],651⟩,⟨171,(2),[3,4,8,12,15,16],[10],652⟩,⟨171,(3),[3,4,8,12,15,16],[10],653⟩,⟨172,(0),[4,8,12,16],[10],1291⟩,⟨172,(1),[4,8,12,16],[10],1292⟩,⟨172,(2),[4,8,12,16],[10],1293⟩,⟨172,(3),[4,8,12,16],[10],1294⟩,⟨172,(4),[4,8,12,16],[10],1295⟩,⟨172,(5),[4,8,12,16],[10],1292⟩,⟨172,(6),[4,8,12,16],[10],1293⟩,⟨172,(7),[4,8,12,16],[10],1294⟩,⟨172,(8),[4,8,12,16],[10],1291⟩,⟨172,(9),[4,8,12,16],[10],1292⟩,⟨172,(10),[4,8,12,16],[10],1293⟩,⟨172,(11),[4,8,12,16],[10],1294⟩,⟨172,(12),[4,8,12,16],[10],1296⟩,⟨172,(13),[4,8,12,16],[10],1292⟩,⟨172,(14),[4,8,12,16],[10],1293⟩,⟨172,(15),[4,8,12,16],[10],1294⟩,⟨175,(0),[3,4,8,12,15,16],[10],654⟩,⟨175,(1),[3,4,8,12,15,16],[10],655⟩,⟨175,(2),[3,4,8,12,15,16],[10],656⟩,⟨175,(3),[3,4,8,12,15,16],[10],657⟩,⟨175,(4),[3,4,8,12,15,16],[10],654⟩,⟨175,(5),[3,4,8,12,15,16],[10],655⟩,⟨175,(6),[3,4,8,12,15,16],[10],658⟩,⟨175,(7),[3,4,8,12,15,16],[10],657⟩,⟨175,(8),[3,4,8,12,15,16],[10],654⟩,⟨175,(9),[3,4,8,12,15,16],[10],655⟩,⟨175,(10),[3,4,8,12,15,16],[10],656⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1248
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1249
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1250
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1251
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1252
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1253
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1254
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1255
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1256
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1257
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1258
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1259
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1260
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1261
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1262
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1263
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1264
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1265
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1266
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1267
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1268
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1269
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1270
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1271
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1272
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1273
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1274
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1275
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1276
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1277
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1278
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1279
end Section14Records_4_1248_1280

#print axioms solution
