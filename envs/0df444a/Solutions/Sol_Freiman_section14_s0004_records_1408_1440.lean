-- Prove2me | solution 1 for Freiman.section14_s0004_records_1408_1440
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:40:58.092762+00:00
-- url     : https://prove2.me/submissions/25c65802-648a-4352-bb40-470bd8ff9c4d

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
namespace Section14Records_4_1408_1440
private theorem valid1408 : RecordDataValid section14Catalog 4 (⟨192,(18),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1409 : RecordDataValid section14Catalog 4 (⟨192,(19),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1410 : RecordDataValid section14Catalog 4 (⟨192,(20),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1411 : RecordDataValid section14Catalog 4 (⟨192,(21),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1412 : RecordDataValid section14Catalog 4 (⟨192,(22),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1413 : RecordDataValid section14Catalog 4 (⟨192,(23),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1414 : RecordDataValid section14Catalog 4 (⟨192,(24),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1415 : RecordDataValid section14Catalog 4 (⟨195,(0),[3,4,8,12,15,16],[10],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1416 : RecordDataValid section14Catalog 4 (⟨195,(1),[3,4,8,12,15,16],[10],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1417 : RecordDataValid section14Catalog 4 (⟨195,(2),[3,4,8,12,15,16],[10],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1418 : RecordDataValid section14Catalog 4 (⟨195,(3),[3,4,8,12,15,16],[10],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1419 : RecordDataValid section14Catalog 4 (⟨195,(4),[3,4,8,12,15,16],[10],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1420 : RecordDataValid section14Catalog 4 (⟨195,(5),[3,4,8,12,15,16],[10],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1421 : RecordDataValid section14Catalog 4 (⟨195,(6),[3,4,8,12,15,16],[10],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1422 : RecordDataValid section14Catalog 4 (⟨195,(7),[3,4,8,12,15,16],[10],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1423 : RecordDataValid section14Catalog 4 (⟨195,(8),[3,4,7,15,16],[10],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1424 : RecordDataValid section14Catalog 4 (⟨195,(9),[3,4,7,15,16],[10],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1425 : RecordDataValid section14Catalog 4 (⟨197,(0),[4,8,12,16],[10],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1426 : RecordDataValid section14Catalog 4 (⟨197,(1),[4,8,12,16],[10],1323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1323,[4,8,9,12,16],1327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1427 : RecordDataValid section14Catalog 4 (⟨197,(2),[4,8,12,16],[10],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1428 : RecordDataValid section14Catalog 4 (⟨197,(3),[4,8,12,16],[10],1324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1324,[4,8,9,12,16],1328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1429 : RecordDataValid section14Catalog 4 (⟨197,(4),[4,8,12,16],[10],1325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1325,[4,8,9,12,16],1329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1430 : RecordDataValid section14Catalog 4 (⟨197,(5),[4,8,12,16],[10],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1431 : RecordDataValid section14Catalog 4 (⟨197,(6),[4,8,12,16],[10],1323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1323,[4,8,9,12,16],1327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1432 : RecordDataValid section14Catalog 4 (⟨197,(7),[4,8,12,16],[10],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1433 : RecordDataValid section14Catalog 4 (⟨197,(8),[4,8,12,16],[10],1324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1324,[4,8,9,12,16],1328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1434 : RecordDataValid section14Catalog 4 (⟨197,(9),[4,8,12,16],[10],1325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1325,[4,8,9,12,16],1329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1435 : RecordDataValid section14Catalog 4 (⟨197,(10),[4,8,12,16],[10],1326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1326,[4,8,9,12,16],1330⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1436 : RecordDataValid section14Catalog 4 (⟨197,(11),[4,8,12,16],[10],1326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1326,[4,8,9,12,16],1330⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1437 : RecordDataValid section14Catalog 4 (⟨197,(12),[4,8,12,16],[10],1326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1326,[4,8,9,12,16],1330⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1438 : RecordDataValid section14Catalog 4 (⟨197,(13),[4,8,12,16],[10],1326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1326,[4,8,9,12,16],1330⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1439 : RecordDataValid section14Catalog 4 (⟨197,(14),[4,8,12,16],[10],1325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1325,[4,8,9,12,16],1329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1408).take 32 = [⟨192,(18),[4,8,12,16],[10],1320⟩,⟨192,(19),[4,8,12,16],[10],1320⟩,⟨192,(20),[4,8,12,16],[10],1321⟩,⟨192,(21),[4,8,12,16],[10],1321⟩,⟨192,(22),[4,8,12,16],[10],1321⟩,⟨192,(23),[4,8,12,16],[10],1321⟩,⟨192,(24),[4,8,12,16],[10],1321⟩,⟨195,(0),[3,4,8,12,15,16],[10],697⟩,⟨195,(1),[3,4,8,12,15,16],[10],697⟩,⟨195,(2),[3,4,8,12,15,16],[10],698⟩,⟨195,(3),[3,4,8,12,15,16],[10],698⟩,⟨195,(4),[3,4,8,12,15,16],[10],699⟩,⟨195,(5),[3,4,8,12,15,16],[10],700⟩,⟨195,(6),[3,4,8,12,15,16],[10],699⟩,⟨195,(7),[3,4,8,12,15,16],[10],701⟩,⟨195,(8),[3,4,7,15,16],[10],702⟩,⟨195,(9),[3,4,7,15,16],[10],703⟩,⟨197,(0),[4,8,12,16],[10],1322⟩,⟨197,(1),[4,8,12,16],[10],1323⟩,⟨197,(2),[4,8,12,16],[10],1322⟩,⟨197,(3),[4,8,12,16],[10],1324⟩,⟨197,(4),[4,8,12,16],[10],1325⟩,⟨197,(5),[4,8,12,16],[10],1322⟩,⟨197,(6),[4,8,12,16],[10],1323⟩,⟨197,(7),[4,8,12,16],[10],1322⟩,⟨197,(8),[4,8,12,16],[10],1324⟩,⟨197,(9),[4,8,12,16],[10],1325⟩,⟨197,(10),[4,8,12,16],[10],1326⟩,⟨197,(11),[4,8,12,16],[10],1326⟩,⟨197,(12),[4,8,12,16],[10],1326⟩,⟨197,(13),[4,8,12,16],[10],1326⟩,⟨197,(14),[4,8,12,16],[10],1325⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1408
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1409
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1410
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1411
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1412
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1413
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1414
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1415
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1416
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1417
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1418
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1419
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1420
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1421
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1422
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1423
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1424
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1425
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1426
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1427
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1428
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1429
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1430
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1431
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1432
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1433
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1434
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1435
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1436
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1437
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1438
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1439
end Section14Records_4_1408_1440

#print axioms solution
