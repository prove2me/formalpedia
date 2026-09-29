-- Prove2me | solution 1 for Freiman.section14_s0008_records_1472_1504
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:29:09.723715+00:00
-- url     : https://prove2.me/submissions/e281958b-6832-4189-8f76-0a6c45e363ac

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
namespace Section14Records_8_1472_1504
private theorem valid1472 : RecordDataValid section14Catalog 8 (⟨207,(6),[4,8,12,16],[10],1337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1337,[4,8,9,12,16],1341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1473 : RecordDataValid section14Catalog 8 (⟨207,(7),[4,8,12,16],[10],1336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1336,[4,8,9,12,16],1340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1474 : RecordDataValid section14Catalog 8 (⟨207,(8),[4,8,12,16],[10],1338⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1338,[4,8,9,12,16],1342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1475 : RecordDataValid section14Catalog 8 (⟨207,(9),[4,8,12,16],[10],1339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1339,[4,8,9,12,16],1343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1476 : RecordDataValid section14Catalog 8 (⟨207,(10),[4,8,12,16],[10],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1477 : RecordDataValid section14Catalog 8 (⟨207,(11),[4,8,12,16],[10],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1478 : RecordDataValid section14Catalog 8 (⟨207,(12),[4,8,12,16],[10],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1479 : RecordDataValid section14Catalog 8 (⟨207,(13),[4,8,12,16],[10],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1480 : RecordDataValid section14Catalog 8 (⟨207,(14),[4,8,12,16],[10],1339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1339,[4,8,9,12,16],1343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1481 : RecordDataValid section14Catalog 8 (⟨207,(15),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1482 : RecordDataValid section14Catalog 8 (⟨207,(16),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1483 : RecordDataValid section14Catalog 8 (⟨207,(17),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1484 : RecordDataValid section14Catalog 8 (⟨207,(18),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1485 : RecordDataValid section14Catalog 8 (⟨207,(19),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1486 : RecordDataValid section14Catalog 8 (⟨207,(20),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1487 : RecordDataValid section14Catalog 8 (⟨207,(21),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1488 : RecordDataValid section14Catalog 8 (⟨207,(22),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1489 : RecordDataValid section14Catalog 8 (⟨207,(23),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1490 : RecordDataValid section14Catalog 8 (⟨207,(24),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1491 : RecordDataValid section14Catalog 8 (⟨210,(0),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1492 : RecordDataValid section14Catalog 8 (⟨210,(1),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1493 : RecordDataValid section14Catalog 8 (⟨210,(2),[4,8,12,16],[10],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1494 : RecordDataValid section14Catalog 8 (⟨210,(3),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1495 : RecordDataValid section14Catalog 8 (⟨210,(4),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1496 : RecordDataValid section14Catalog 8 (⟨210,(5),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1497 : RecordDataValid section14Catalog 8 (⟨210,(6),[4,8,12,16],[10],726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨726,[1,2,4,5,6,8,9,10,12,13,14,16],727⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1498 : RecordDataValid section14Catalog 8 (⟨210,(7),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1499 : RecordDataValid section14Catalog 8 (⟨210,(8),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1500 : RecordDataValid section14Catalog 8 (⟨210,(9),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1501 : RecordDataValid section14Catalog 8 (⟨210,(10),[4,8,12,16],[10],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1502 : RecordDataValid section14Catalog 8 (⟨210,(11),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1503 : RecordDataValid section14Catalog 8 (⟨210,(12),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1472).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1472).take 32 = [⟨207,(6),[4,8,12,16],[10],1337⟩,⟨207,(7),[4,8,12,16],[10],1336⟩,⟨207,(8),[4,8,12,16],[10],1338⟩,⟨207,(9),[4,8,12,16],[10],1339⟩,⟨207,(10),[4,8,12,16],[10],1340⟩,⟨207,(11),[4,8,12,16],[10],1340⟩,⟨207,(12),[4,8,12,16],[10],1340⟩,⟨207,(13),[4,8,12,16],[10],1340⟩,⟨207,(14),[4,8,12,16],[10],1339⟩,⟨207,(15),[4,8,12,16],[10],1341⟩,⟨207,(16),[4,8,12,16],[10],1341⟩,⟨207,(17),[4,8,12,16],[10],1341⟩,⟨207,(18),[4,8,12,16],[10],1341⟩,⟨207,(19),[4,8,12,16],[10],1341⟩,⟨207,(20),[4,8,12,16],[10],1342⟩,⟨207,(21),[4,8,12,16],[10],1342⟩,⟨207,(22),[4,8,12,16],[10],1342⟩,⟨207,(23),[4,8,12,16],[10],1342⟩,⟨207,(24),[4,8,12,16],[10],1342⟩,⟨210,(0),[4,8,12,16],[10],722⟩,⟨210,(1),[4,8,12,16],[10],723⟩,⟨210,(2),[4,8,12,16],[10],724⟩,⟨210,(3),[4,8,12,16],[10],725⟩,⟨210,(4),[4,8,12,16],[10],722⟩,⟨210,(5),[4,8,12,16],[10],723⟩,⟨210,(6),[4,8,12,16],[10],726⟩,⟨210,(7),[4,8,12,16],[10],725⟩,⟨210,(8),[4,8,12,16],[10],722⟩,⟨210,(9),[4,8,12,16],[10],723⟩,⟨210,(10),[4,8,12,16],[10],724⟩,⟨210,(11),[4,8,12,16],[10],725⟩,⟨210,(12),[4,8,12,16],[10],722⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1472
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1473
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1474
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1475
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1476
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1477
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1478
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1479
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1480
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1481
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1482
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1483
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1484
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1485
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1486
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1487
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1488
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1489
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1490
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1491
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1492
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1493
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1494
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1495
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1496
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1497
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1498
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1499
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1500
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1501
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1502
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1503
end Section14Records_8_1472_1504

#print axioms solution
