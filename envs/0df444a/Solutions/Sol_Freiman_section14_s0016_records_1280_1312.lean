-- Prove2me | solution 1 for Freiman.section14_s0016_records_1280_1312
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:26:12.243354+00:00
-- url     : https://prove2.me/submissions/56f6e6b7-c8cb-444b-8d72-2164fd9800ac

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
namespace Section14Records_16_1280_1312
private theorem valid1280 : RecordDataValid section14Catalog 16 (⟨210,(3),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1281 : RecordDataValid section14Catalog 16 (⟨210,(4),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1282 : RecordDataValid section14Catalog 16 (⟨210,(5),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1283 : RecordDataValid section14Catalog 16 (⟨210,(6),[4,8,12,16],[10],726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨726,[1,2,4,5,6,8,9,10,12,13,14,16],727⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1284 : RecordDataValid section14Catalog 16 (⟨210,(7),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1285 : RecordDataValid section14Catalog 16 (⟨210,(8),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1286 : RecordDataValid section14Catalog 16 (⟨210,(9),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1287 : RecordDataValid section14Catalog 16 (⟨210,(10),[4,8,12,16],[10],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1288 : RecordDataValid section14Catalog 16 (⟨210,(11),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1289 : RecordDataValid section14Catalog 16 (⟨210,(12),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1290 : RecordDataValid section14Catalog 16 (⟨210,(13),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1291 : RecordDataValid section14Catalog 16 (⟨210,(14),[4,8,12,16],[10],727⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨727,[1,2,4,5,6,8,9,10,12,13,14,16],728⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1292 : RecordDataValid section14Catalog 16 (⟨210,(15),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1293 : RecordDataValid section14Catalog 16 (⟨213,(0),[4,8,12,16],[10],1343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1343,[4,8,9,12,16],1347⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1294 : RecordDataValid section14Catalog 16 (⟨213,(1),[4,8,12,16],[10],1344⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1344,[4,8,9,12,16],1348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1295 : RecordDataValid section14Catalog 16 (⟨213,(2),[4,8,12,16],[10],1343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1343,[4,8,9,12,16],1347⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1296 : RecordDataValid section14Catalog 16 (⟨213,(3),[4,8,12,16],[10],1345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1345,[4,8,9,12,16],1349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1297 : RecordDataValid section14Catalog 16 (⟨213,(4),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1298 : RecordDataValid section14Catalog 16 (⟨213,(5),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1299 : RecordDataValid section14Catalog 16 (⟨213,(6),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1300 : RecordDataValid section14Catalog 16 (⟨213,(7),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1301 : RecordDataValid section14Catalog 16 (⟨213,(8),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1302 : RecordDataValid section14Catalog 16 (⟨213,(9),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1303 : RecordDataValid section14Catalog 16 (⟨213,(10),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1304 : RecordDataValid section14Catalog 16 (⟨213,(11),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1305 : RecordDataValid section14Catalog 16 (⟨213,(12),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1306 : RecordDataValid section14Catalog 16 (⟨213,(13),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1307 : RecordDataValid section14Catalog 16 (⟨213,(14),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1308 : RecordDataValid section14Catalog 16 (⟨213,(15),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1309 : RecordDataValid section14Catalog 16 (⟨220,(0),[4,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1310 : RecordDataValid section14Catalog 16 (⟨220,(1),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1311 : RecordDataValid section14Catalog 16 (⟨220,(2),[4,8,12,16],[10],1266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1266,[4,8,12,16],1270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1280).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1280).take 32 = [⟨210,(3),[4,8,12,16],[10],725⟩,⟨210,(4),[4,8,12,16],[10],722⟩,⟨210,(5),[4,8,12,16],[10],723⟩,⟨210,(6),[4,8,12,16],[10],726⟩,⟨210,(7),[4,8,12,16],[10],725⟩,⟨210,(8),[4,8,12,16],[10],722⟩,⟨210,(9),[4,8,12,16],[10],723⟩,⟨210,(10),[4,8,12,16],[10],724⟩,⟨210,(11),[4,8,12,16],[10],725⟩,⟨210,(12),[4,8,12,16],[10],722⟩,⟨210,(13),[4,8,12,16],[10],723⟩,⟨210,(14),[4,8,12,16],[10],727⟩,⟨210,(15),[4,8,12,16],[10],725⟩,⟨213,(0),[4,8,12,16],[10],1343⟩,⟨213,(1),[4,8,12,16],[10],1344⟩,⟨213,(2),[4,8,12,16],[10],1343⟩,⟨213,(3),[4,8,12,16],[10],1345⟩,⟨213,(4),[4,8,12,16],[10],1346⟩,⟨213,(5),[4,8,12,16],[10],1346⟩,⟨213,(6),[4,8,12,16],[10],1346⟩,⟨213,(7),[4,8,12,16],[10],1346⟩,⟨213,(8),[4,8,12,16],[10],1347⟩,⟨213,(9),[4,8,12,16],[10],1347⟩,⟨213,(10),[4,8,12,16],[10],1347⟩,⟨213,(11),[4,8,12,16],[10],1347⟩,⟨213,(12),[4,8,12,16],[10],1348⟩,⟨213,(13),[4,8,12,16],[10],1348⟩,⟨213,(14),[4,8,12,16],[10],1348⟩,⟨213,(15),[4,8,12,16],[10],1348⟩,⟨220,(0),[4,16],[10],3⟩,⟨220,(1),[4,8,12,16],[10],3⟩,⟨220,(2),[4,8,12,16],[10],1266⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1280
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1281
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1282
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1283
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1284
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1285
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1286
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1287
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1288
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1289
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1290
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1291
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1292
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1293
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1294
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1295
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1296
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1297
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1298
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1299
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1300
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1301
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1302
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1303
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1304
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1305
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1306
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1307
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1308
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1309
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1310
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1311
end Section14Records_16_1280_1312

#print axioms solution
