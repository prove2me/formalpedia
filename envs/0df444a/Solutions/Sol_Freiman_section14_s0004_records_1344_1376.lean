-- Prove2me | solution 1 for Freiman.section14_s0004_records_1344_1376
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:39:00.420081+00:00
-- url     : https://prove2.me/submissions/1292d5b7-0074-4b9f-9169-864b277a550c

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
namespace Section14Records_4_1344_1376
private theorem valid1344 : RecordDataValid section14Catalog 4 (⟨185,(11),[3,4,8,12,15,16],[10],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1345 : RecordDataValid section14Catalog 4 (⟨185,(12),[3,4,8,12,15,16],[10],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1346 : RecordDataValid section14Catalog 4 (⟨185,(13),[3,4,8,12,15,16],[10],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1347 : RecordDataValid section14Catalog 4 (⟨185,(14),[3,4,8,12,15,16],[10],683⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨683,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],684⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1348 : RecordDataValid section14Catalog 4 (⟨185,(15),[3,4,8,12,15,16],[10],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1349 : RecordDataValid section14Catalog 4 (⟨188,(0),[4,8,12,16],[10],1309⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1309,[4,8,9,12,16],1313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1350 : RecordDataValid section14Catalog 4 (⟨188,(1),[4,8,12,16],[10],1310⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1310,[4,8,9,12,16],1314⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1351 : RecordDataValid section14Catalog 4 (⟨188,(2),[4,8,12,16],[10],1309⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1309,[4,8,9,12,16],1313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1352 : RecordDataValid section14Catalog 4 (⟨188,(3),[4,8,12,16],[10],1311⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1311,[4,8,9,12,16],1315⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1353 : RecordDataValid section14Catalog 4 (⟨188,(4),[4,8,12,16],[10],1312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1312,[4,8,9,12,16],1316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1354 : RecordDataValid section14Catalog 4 (⟨188,(5),[4,8,12,16],[10],1312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1312,[4,8,9,12,16],1316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1355 : RecordDataValid section14Catalog 4 (⟨188,(6),[4,8,12,16],[10],1312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1312,[4,8,9,12,16],1316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1356 : RecordDataValid section14Catalog 4 (⟨188,(7),[4,8,12,16],[10],1312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1312,[4,8,9,12,16],1316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1357 : RecordDataValid section14Catalog 4 (⟨188,(8),[4,8,12,16],[10],1313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1313,[4,8,9,12,16],1317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1358 : RecordDataValid section14Catalog 4 (⟨188,(9),[4,8,12,16],[10],1313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1313,[4,8,9,12,16],1317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1359 : RecordDataValid section14Catalog 4 (⟨188,(10),[4,8,12,16],[10],1313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1313,[4,8,9,12,16],1317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1360 : RecordDataValid section14Catalog 4 (⟨188,(11),[4,8,12,16],[10],1313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1313,[4,8,9,12,16],1317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1361 : RecordDataValid section14Catalog 4 (⟨188,(12),[4,8,12,16],[10],1314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1314,[4,8,9,12,16],1318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1362 : RecordDataValid section14Catalog 4 (⟨188,(13),[4,8,12,16],[10],1314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1314,[4,8,9,12,16],1318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1363 : RecordDataValid section14Catalog 4 (⟨188,(14),[4,8,12,16],[10],1314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1314,[4,8,9,12,16],1318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1364 : RecordDataValid section14Catalog 4 (⟨188,(15),[4,8,12,16],[10],1314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1314,[4,8,9,12,16],1318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1365 : RecordDataValid section14Catalog 4 (⟨190,(0),[3,4,8,12,15,16],[10],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1366 : RecordDataValid section14Catalog 4 (⟨190,(1),[3,4,8,12,15,16],[10],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1367 : RecordDataValid section14Catalog 4 (⟨190,(2),[3,4,8,12,15,16],[10],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1368 : RecordDataValid section14Catalog 4 (⟨190,(3),[3,4,8,12,15,16],[10],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1369 : RecordDataValid section14Catalog 4 (⟨190,(4),[3,4,8,12,15,16],[10],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1370 : RecordDataValid section14Catalog 4 (⟨190,(5),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1371 : RecordDataValid section14Catalog 4 (⟨190,(6),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1372 : RecordDataValid section14Catalog 4 (⟨190,(7),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1373 : RecordDataValid section14Catalog 4 (⟨190,(8),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1374 : RecordDataValid section14Catalog 4 (⟨190,(9),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1375 : RecordDataValid section14Catalog 4 (⟨190,(10),[3,4,8,12,15,16],[10],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1344).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1344).take 32 = [⟨185,(11),[3,4,8,12,15,16],[10],681⟩,⟨185,(12),[3,4,8,12,15,16],[10],678⟩,⟨185,(13),[3,4,8,12,15,16],[10],679⟩,⟨185,(14),[3,4,8,12,15,16],[10],683⟩,⟨185,(15),[3,4,8,12,15,16],[10],681⟩,⟨188,(0),[4,8,12,16],[10],1309⟩,⟨188,(1),[4,8,12,16],[10],1310⟩,⟨188,(2),[4,8,12,16],[10],1309⟩,⟨188,(3),[4,8,12,16],[10],1311⟩,⟨188,(4),[4,8,12,16],[10],1312⟩,⟨188,(5),[4,8,12,16],[10],1312⟩,⟨188,(6),[4,8,12,16],[10],1312⟩,⟨188,(7),[4,8,12,16],[10],1312⟩,⟨188,(8),[4,8,12,16],[10],1313⟩,⟨188,(9),[4,8,12,16],[10],1313⟩,⟨188,(10),[4,8,12,16],[10],1313⟩,⟨188,(11),[4,8,12,16],[10],1313⟩,⟨188,(12),[4,8,12,16],[10],1314⟩,⟨188,(13),[4,8,12,16],[10],1314⟩,⟨188,(14),[4,8,12,16],[10],1314⟩,⟨188,(15),[4,8,12,16],[10],1314⟩,⟨190,(0),[3,4,8,12,15,16],[10],690⟩,⟨190,(1),[3,4,8,12,15,16],[10],690⟩,⟨190,(2),[3,4,8,12,15,16],[10],690⟩,⟨190,(3),[3,4,8,12,15,16],[10],690⟩,⟨190,(4),[3,4,8,12,15,16],[10],690⟩,⟨190,(5),[3,4,8,12,15,16],[10],691⟩,⟨190,(6),[3,4,8,12,15,16],[10],691⟩,⟨190,(7),[3,4,8,12,15,16],[10],691⟩,⟨190,(8),[3,4,8,12,15,16],[10],691⟩,⟨190,(9),[3,4,8,12,15,16],[10],691⟩,⟨190,(10),[3,4,8,12,15,16],[10],692⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1344
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1345
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1346
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1347
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1348
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1349
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1350
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1351
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1352
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1353
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1354
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1355
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1356
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1357
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1358
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1359
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1360
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1361
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1362
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1363
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1364
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1365
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1366
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1367
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1368
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1369
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1370
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1371
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1372
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1373
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1374
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1375
end Section14Records_4_1344_1376

#print axioms solution
