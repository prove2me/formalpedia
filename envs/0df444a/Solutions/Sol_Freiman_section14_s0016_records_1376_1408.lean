-- Prove2me | solution 1 for Freiman.section14_s0016_records_1376_1408
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:29:23.327572+00:00
-- url     : https://prove2.me/submissions/d300704e-d59e-41a2-9e9b-493d289c0eff

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
namespace Section14Records_16_1376_1408
private theorem valid1376 : RecordDataValid section14Catalog 16 (⟨222,(22),[3,4,7,8,12,15,16],[10],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1377 : RecordDataValid section14Catalog 16 (⟨222,(23),[3,4,7,8,12,15,16],[10],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1378 : RecordDataValid section14Catalog 16 (⟨222,(24),[3,4,7,15,16],[10],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1379 : RecordDataValid section14Catalog 16 (⟨224,(0),[3,4,7,8,12,15,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1380 : RecordDataValid section14Catalog 16 (⟨224,(1),[3,4,7,8,12,15,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1381 : RecordDataValid section14Catalog 16 (⟨224,(2),[3,4,7,8,12,15,16],[10],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1382 : RecordDataValid section14Catalog 16 (⟨224,(3),[3,4,7,8,12,15,16],[10],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1383 : RecordDataValid section14Catalog 16 (⟨224,(4),[3,4,7,8,12,15,16],[10],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1384 : RecordDataValid section14Catalog 16 (⟨224,(5),[4,8,12,16],[10],1363⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1363,[4,8,9,12,16],1367⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1385 : RecordDataValid section14Catalog 16 (⟨224,(6),[4,8,12,16],[10],1363⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1363,[4,8,9,12,16],1367⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1386 : RecordDataValid section14Catalog 16 (⟨224,(7),[4,8,12,16],[10],1364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1364,[4,8,9,12,16],1368⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1387 : RecordDataValid section14Catalog 16 (⟨224,(8),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1388 : RecordDataValid section14Catalog 16 (⟨224,(9),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1389 : RecordDataValid section14Catalog 16 (⟨224,(10),[4,8,12,16],[10],1365⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1365,[4,8,9,12,16],1369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1390 : RecordDataValid section14Catalog 16 (⟨224,(11),[4,8,12,16],[10],1365⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1365,[4,8,9,12,16],1369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1391 : RecordDataValid section14Catalog 16 (⟨224,(12),[4,8,12,16],[10],1364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1364,[4,8,9,12,16],1368⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1392 : RecordDataValid section14Catalog 16 (⟨224,(13),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1393 : RecordDataValid section14Catalog 16 (⟨224,(14),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1394 : RecordDataValid section14Catalog 16 (⟨224,(15),[4,8,12,16],[10],1366⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1366,[4,8,9,12,16],1370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1395 : RecordDataValid section14Catalog 16 (⟨224,(16),[4,8,12,16],[10],1366⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1366,[4,8,9,12,16],1370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1396 : RecordDataValid section14Catalog 16 (⟨224,(17),[4,8,12,16],[10],1364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1364,[4,8,9,12,16],1368⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1397 : RecordDataValid section14Catalog 16 (⟨224,(18),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1398 : RecordDataValid section14Catalog 16 (⟨224,(19),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1399 : RecordDataValid section14Catalog 16 (⟨224,(20),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1400 : RecordDataValid section14Catalog 16 (⟨224,(21),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1401 : RecordDataValid section14Catalog 16 (⟨224,(22),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1402 : RecordDataValid section14Catalog 16 (⟨224,(23),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1403 : RecordDataValid section14Catalog 16 (⟨224,(24),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1404 : RecordDataValid section14Catalog 16 (⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1405 : RecordDataValid section14Catalog 16 (⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1406 : RecordDataValid section14Catalog 16 (⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1407 : RecordDataValid section14Catalog 16 (⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1376).take 32 = [⟨222,(22),[3,4,7,8,12,15,16],[10],537⟩,⟨222,(23),[3,4,7,8,12,15,16],[10],538⟩,⟨222,(24),[3,4,7,15,16],[10],537⟩,⟨224,(0),[3,4,7,8,12,15,16],[10],539⟩,⟨224,(1),[3,4,7,8,12,15,16],[10],539⟩,⟨224,(2),[3,4,7,8,12,15,16],[10],540⟩,⟨224,(3),[3,4,7,8,12,15,16],[10],541⟩,⟨224,(4),[3,4,7,8,12,15,16],[10],542⟩,⟨224,(5),[4,8,12,16],[10],1363⟩,⟨224,(6),[4,8,12,16],[10],1363⟩,⟨224,(7),[4,8,12,16],[10],1364⟩,⟨224,(8),[4,8,12,16],[10],1355⟩,⟨224,(9),[4,8,12,16],[10],1356⟩,⟨224,(10),[4,8,12,16],[10],1365⟩,⟨224,(11),[4,8,12,16],[10],1365⟩,⟨224,(12),[4,8,12,16],[10],1364⟩,⟨224,(13),[4,8,12,16],[10],1355⟩,⟨224,(14),[4,8,12,16],[10],1356⟩,⟨224,(15),[4,8,12,16],[10],1366⟩,⟨224,(16),[4,8,12,16],[10],1366⟩,⟨224,(17),[4,8,12,16],[10],1364⟩,⟨224,(18),[4,8,12,16],[10],1355⟩,⟨224,(19),[4,8,12,16],[10],1356⟩,⟨224,(20),[4,8,12,16],[10],1367⟩,⟨224,(21),[4,8,12,16],[10],1367⟩,⟨224,(22),[4,8,12,16],[10],1367⟩,⟨224,(23),[4,8,12,16],[10],1355⟩,⟨224,(24),[4,8,12,16],[10],1356⟩,⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩,⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩,⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩,⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1376
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1377
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1378
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1379
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1380
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1381
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1382
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1383
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1384
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1385
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1386
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1387
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1388
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1389
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1390
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1391
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1392
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1393
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1394
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1395
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1396
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1397
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1398
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1399
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1400
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1401
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1402
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1403
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1404
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1405
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1406
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1407
end Section14Records_16_1376_1408

#print axioms solution
