-- Prove2me | solution 1 for Freiman.section14_s0004_records_1376_1408
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:39:07.290463+00:00
-- url     : https://prove2.me/submissions/2c6e6380-c0df-491a-a577-3d061245fa03

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
namespace Section14Records_4_1376_1408
private theorem valid1376 : RecordDataValid section14Catalog 4 (⟨190,(11),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1377 : RecordDataValid section14Catalog 4 (⟨190,(12),[3,4,8,12,15,16],[10],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1378 : RecordDataValid section14Catalog 4 (⟨190,(13),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1379 : RecordDataValid section14Catalog 4 (⟨190,(14),[3,4,8,12,15,16],[10],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1380 : RecordDataValid section14Catalog 4 (⟨190,(15),[3,4,8,12,15,16],[10],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1381 : RecordDataValid section14Catalog 4 (⟨190,(16),[3,4,8,12,15,16],[10],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1382 : RecordDataValid section14Catalog 4 (⟨190,(17),[3,4,8,12,15,16],[10],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1383 : RecordDataValid section14Catalog 4 (⟨190,(18),[3,4,8,12,15,16],[10],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1384 : RecordDataValid section14Catalog 4 (⟨190,(19),[3,4,8,12,15,16],[10],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1385 : RecordDataValid section14Catalog 4 (⟨190,(20),[3,4,8,12,15,16],[10],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1386 : RecordDataValid section14Catalog 4 (⟨190,(21),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1387 : RecordDataValid section14Catalog 4 (⟨190,(22),[3,4,8,12,15,16],[10],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1388 : RecordDataValid section14Catalog 4 (⟨190,(23),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1389 : RecordDataValid section14Catalog 4 (⟨190,(24),[3,4,8,12,15,16],[10],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1390 : RecordDataValid section14Catalog 4 (⟨192,(0),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1391 : RecordDataValid section14Catalog 4 (⟨192,(1),[4,8,12,16],[10],1316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1316,[4,8,9,12,16],1320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1392 : RecordDataValid section14Catalog 4 (⟨192,(2),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1393 : RecordDataValid section14Catalog 4 (⟨192,(3),[4,8,12,16],[10],1317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1317,[4,8,9,12,16],1321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1394 : RecordDataValid section14Catalog 4 (⟨192,(4),[4,8,12,16],[10],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1395 : RecordDataValid section14Catalog 4 (⟨192,(5),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1396 : RecordDataValid section14Catalog 4 (⟨192,(6),[4,8,12,16],[10],1316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1316,[4,8,9,12,16],1320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1397 : RecordDataValid section14Catalog 4 (⟨192,(7),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1398 : RecordDataValid section14Catalog 4 (⟨192,(8),[4,8,12,16],[10],1317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1317,[4,8,9,12,16],1321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1399 : RecordDataValid section14Catalog 4 (⟨192,(9),[4,8,12,16],[10],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1400 : RecordDataValid section14Catalog 4 (⟨192,(10),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1401 : RecordDataValid section14Catalog 4 (⟨192,(11),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1402 : RecordDataValid section14Catalog 4 (⟨192,(12),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1403 : RecordDataValid section14Catalog 4 (⟨192,(13),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1404 : RecordDataValid section14Catalog 4 (⟨192,(14),[4,8,12,16],[10],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1405 : RecordDataValid section14Catalog 4 (⟨192,(15),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1406 : RecordDataValid section14Catalog 4 (⟨192,(16),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1407 : RecordDataValid section14Catalog 4 (⟨192,(17),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1376).take 32 = [⟨190,(11),[3,4,8,12,15,16],[10],693⟩,⟨190,(12),[3,4,8,12,15,16],[10],694⟩,⟨190,(13),[3,4,8,12,15,16],[10],693⟩,⟨190,(14),[3,4,8,12,15,16],[10],695⟩,⟨190,(15),[3,4,8,12,15,16],[10],692⟩,⟨190,(16),[3,4,8,12,15,16],[10],696⟩,⟨190,(17),[3,4,8,12,15,16],[10],696⟩,⟨190,(18),[3,4,8,12,15,16],[10],696⟩,⟨190,(19),[3,4,8,12,15,16],[10],696⟩,⟨190,(20),[3,4,8,12,15,16],[10],692⟩,⟨190,(21),[3,4,8,12,15,16],[10],693⟩,⟨190,(22),[3,4,8,12,15,16],[10],694⟩,⟨190,(23),[3,4,8,12,15,16],[10],693⟩,⟨190,(24),[3,4,8,12,15,16],[10],695⟩,⟨192,(0),[4,8,12,16],[10],1315⟩,⟨192,(1),[4,8,12,16],[10],1316⟩,⟨192,(2),[4,8,12,16],[10],1315⟩,⟨192,(3),[4,8,12,16],[10],1317⟩,⟨192,(4),[4,8,12,16],[10],1318⟩,⟨192,(5),[4,8,12,16],[10],1315⟩,⟨192,(6),[4,8,12,16],[10],1316⟩,⟨192,(7),[4,8,12,16],[10],1315⟩,⟨192,(8),[4,8,12,16],[10],1317⟩,⟨192,(9),[4,8,12,16],[10],1318⟩,⟨192,(10),[4,8,12,16],[10],1319⟩,⟨192,(11),[4,8,12,16],[10],1319⟩,⟨192,(12),[4,8,12,16],[10],1319⟩,⟨192,(13),[4,8,12,16],[10],1319⟩,⟨192,(14),[4,8,12,16],[10],1318⟩,⟨192,(15),[4,8,12,16],[10],1320⟩,⟨192,(16),[4,8,12,16],[10],1320⟩,⟨192,(17),[4,8,12,16],[10],1320⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1376
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1377
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1378
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1379
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1380
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1381
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1382
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1383
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1384
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1385
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1386
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1387
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1388
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1389
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1390
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1391
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1392
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1393
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1394
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1395
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1396
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1397
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1398
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1399
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1400
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1401
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1402
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1403
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1404
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1405
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1406
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1407
end Section14Records_4_1376_1408

#print axioms solution
