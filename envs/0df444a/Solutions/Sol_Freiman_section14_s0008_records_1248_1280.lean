-- Prove2me | solution 1 for Freiman.section14_s0008_records_1248_1280
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:22:05.860644+00:00
-- url     : https://prove2.me/submissions/cd6a32f9-3c68-4a45-95e1-a86278873009

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
namespace Section14Records_8_1248_1280
private theorem valid1248 : RecordDataValid section14Catalog 8 (⟨180,(6),[3,4,8,12,15,16],[10],670⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨670,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],671⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1249 : RecordDataValid section14Catalog 8 (⟨180,(7),[3,4,8,12,15,16],[10],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1250 : RecordDataValid section14Catalog 8 (⟨180,(8),[3,4,8,12,15,16],[10],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1251 : RecordDataValid section14Catalog 8 (⟨180,(9),[3,4,8,12,15,16],[10],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1252 : RecordDataValid section14Catalog 8 (⟨180,(10),[3,4,8,12,15,16],[10],668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨668,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1253 : RecordDataValid section14Catalog 8 (⟨180,(11),[3,4,8,12,15,16],[10],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1254 : RecordDataValid section14Catalog 8 (⟨180,(12),[3,4,8,12,15,16],[10],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1255 : RecordDataValid section14Catalog 8 (⟨180,(13),[3,4,8,12,15,16],[10],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1256 : RecordDataValid section14Catalog 8 (⟨180,(14),[3,4,8,12,15,16],[10],671⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨671,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],672⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1257 : RecordDataValid section14Catalog 8 (⟨180,(15),[3,4,8,12,15,16],[10],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1258 : RecordDataValid section14Catalog 8 (⟨183,(0),[4,8,12,16],[10],1303⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1303,[4,8,9,12,16],1307⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1259 : RecordDataValid section14Catalog 8 (⟨183,(1),[4,8,12,16],[10],1304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1304,[4,8,9,12,16],1308⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1260 : RecordDataValid section14Catalog 8 (⟨183,(2),[4,8,12,16],[10],1303⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1303,[4,8,9,12,16],1307⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1261 : RecordDataValid section14Catalog 8 (⟨183,(3),[4,8,12,16],[10],1305⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1305,[4,8,9,12,16],1309⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1262 : RecordDataValid section14Catalog 8 (⟨183,(4),[4,8,12,16],[10],1306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1306,[4,8,9,12,16],1310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1263 : RecordDataValid section14Catalog 8 (⟨183,(5),[4,8,12,16],[10],1306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1306,[4,8,9,12,16],1310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1264 : RecordDataValid section14Catalog 8 (⟨183,(6),[4,8,12,16],[10],1306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1306,[4,8,9,12,16],1310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1265 : RecordDataValid section14Catalog 8 (⟨183,(7),[4,8,12,16],[10],1306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1306,[4,8,9,12,16],1310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1266 : RecordDataValid section14Catalog 8 (⟨183,(8),[4,8,12,16],[10],1307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1307,[4,8,9,12,16],1311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1267 : RecordDataValid section14Catalog 8 (⟨183,(9),[4,8,12,16],[10],1307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1307,[4,8,9,12,16],1311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1268 : RecordDataValid section14Catalog 8 (⟨183,(10),[4,8,12,16],[10],1307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1307,[4,8,9,12,16],1311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1269 : RecordDataValid section14Catalog 8 (⟨183,(11),[4,8,12,16],[10],1307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1307,[4,8,9,12,16],1311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1270 : RecordDataValid section14Catalog 8 (⟨183,(12),[4,8,12,16],[10],1308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1308,[4,8,9,12,16],1312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1271 : RecordDataValid section14Catalog 8 (⟨183,(13),[4,8,12,16],[10],1308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1308,[4,8,9,12,16],1312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1272 : RecordDataValid section14Catalog 8 (⟨183,(14),[4,8,12,16],[10],1308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1308,[4,8,9,12,16],1312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1273 : RecordDataValid section14Catalog 8 (⟨183,(15),[4,8,12,16],[10],1308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1308,[4,8,9,12,16],1312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1274 : RecordDataValid section14Catalog 8 (⟨185,(0),[3,4,8,12,15,16],[10],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1275 : RecordDataValid section14Catalog 8 (⟨185,(1),[3,4,8,12,15,16],[10],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1276 : RecordDataValid section14Catalog 8 (⟨185,(2),[3,4,8,12,15,16],[10],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1277 : RecordDataValid section14Catalog 8 (⟨185,(3),[3,4,8,12,15,16],[10],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1278 : RecordDataValid section14Catalog 8 (⟨185,(4),[3,4,8,12,15,16],[10],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1279 : RecordDataValid section14Catalog 8 (⟨185,(5),[3,4,8,12,15,16],[10],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1248).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1248).take 32 = [⟨180,(6),[3,4,8,12,15,16],[10],670⟩,⟨180,(7),[3,4,8,12,15,16],[10],669⟩,⟨180,(8),[3,4,8,12,15,16],[10],666⟩,⟨180,(9),[3,4,8,12,15,16],[10],667⟩,⟨180,(10),[3,4,8,12,15,16],[10],668⟩,⟨180,(11),[3,4,8,12,15,16],[10],669⟩,⟨180,(12),[3,4,8,12,15,16],[10],666⟩,⟨180,(13),[3,4,8,12,15,16],[10],667⟩,⟨180,(14),[3,4,8,12,15,16],[10],671⟩,⟨180,(15),[3,4,8,12,15,16],[10],669⟩,⟨183,(0),[4,8,12,16],[10],1303⟩,⟨183,(1),[4,8,12,16],[10],1304⟩,⟨183,(2),[4,8,12,16],[10],1303⟩,⟨183,(3),[4,8,12,16],[10],1305⟩,⟨183,(4),[4,8,12,16],[10],1306⟩,⟨183,(5),[4,8,12,16],[10],1306⟩,⟨183,(6),[4,8,12,16],[10],1306⟩,⟨183,(7),[4,8,12,16],[10],1306⟩,⟨183,(8),[4,8,12,16],[10],1307⟩,⟨183,(9),[4,8,12,16],[10],1307⟩,⟨183,(10),[4,8,12,16],[10],1307⟩,⟨183,(11),[4,8,12,16],[10],1307⟩,⟨183,(12),[4,8,12,16],[10],1308⟩,⟨183,(13),[4,8,12,16],[10],1308⟩,⟨183,(14),[4,8,12,16],[10],1308⟩,⟨183,(15),[4,8,12,16],[10],1308⟩,⟨185,(0),[3,4,8,12,15,16],[10],678⟩,⟨185,(1),[3,4,8,12,15,16],[10],679⟩,⟨185,(2),[3,4,8,12,15,16],[10],680⟩,⟨185,(3),[3,4,8,12,15,16],[10],681⟩,⟨185,(4),[3,4,8,12,15,16],[10],678⟩,⟨185,(5),[3,4,8,12,15,16],[10],679⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1248
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1249
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1250
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1251
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1252
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1253
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1254
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1255
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1256
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1257
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1258
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1259
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1260
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1261
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1262
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1263
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1264
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1265
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1266
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1267
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1268
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1269
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1270
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1271
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1272
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1273
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1274
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1275
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1276
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1277
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1278
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1279
end Section14Records_8_1248_1280

#print axioms solution
