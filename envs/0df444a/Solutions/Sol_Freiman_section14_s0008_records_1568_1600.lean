-- Prove2me | solution 1 for Freiman.section14_s0008_records_1568_1600
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:32:29.480011+00:00
-- url     : https://prove2.me/submissions/c1595014-f0dd-4997-8117-0a0b9388ef38

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
namespace Section14Records_8_1568_1600
private theorem valid1568 : RecordDataValid section14Catalog 8 (⟨221,(5),[4,8,12,16],[10],1353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1353,[4,8,9,12,16],1357⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1569 : RecordDataValid section14Catalog 8 (⟨221,(6),[4,8,12,16],[10],1353⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1353,[4,8,9,12,16],1357⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1570 : RecordDataValid section14Catalog 8 (⟨221,(7),[4,8,12,16],[10],1354⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1354,[4,8,9,12,16],1358⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1571 : RecordDataValid section14Catalog 8 (⟨221,(8),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1572 : RecordDataValid section14Catalog 8 (⟨221,(9),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1573 : RecordDataValid section14Catalog 8 (⟨221,(10),[4,8,12,16],[10],1357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1357,[4,8,9,12,16],1361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1574 : RecordDataValid section14Catalog 8 (⟨221,(11),[4,8,12,16],[10],1357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1357,[4,8,9,12,16],1361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1575 : RecordDataValid section14Catalog 8 (⟨221,(12),[4,8,12,16],[10],1358⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1358,[4,8,9,12,16],1362⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1576 : RecordDataValid section14Catalog 8 (⟨221,(13),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1577 : RecordDataValid section14Catalog 8 (⟨221,(14),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1578 : RecordDataValid section14Catalog 8 (⟨221,(15),[4,8,12,16],[10],1359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1359,[4,8,9,12,16],1363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1579 : RecordDataValid section14Catalog 8 (⟨221,(16),[4,8,12,16],[10],1359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1359,[4,8,9,12,16],1363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1580 : RecordDataValid section14Catalog 8 (⟨221,(17),[4,8,12,16],[10],1359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1359,[4,8,9,12,16],1363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1581 : RecordDataValid section14Catalog 8 (⟨221,(18),[4,8,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1582 : RecordDataValid section14Catalog 8 (⟨221,(19),[4,8,12,16],[10],1359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1359,[4,8,9,12,16],1363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1583 : RecordDataValid section14Catalog 8 (⟨221,(20),[4,8,12,16],[10],1360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1360,[4,8,9,12,16],1364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1584 : RecordDataValid section14Catalog 8 (⟨221,(21),[4,8,12,16],[10],1360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1360,[4,8,9,12,16],1364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1585 : RecordDataValid section14Catalog 8 (⟨221,(22),[4,8,12,16],[10],1360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1360,[4,8,9,12,16],1364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1586 : RecordDataValid section14Catalog 8 (⟨221,(23),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1587 : RecordDataValid section14Catalog 8 (⟨221,(24),[8,12],[10],1360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1360,[4,8,9,12,16],1364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1588 : RecordDataValid section14Catalog 8 (⟨222,(0),[4,8,12,16],[10],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1589 : RecordDataValid section14Catalog 8 (⟨222,(1),[3,4,8,12,15,16],[10],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1590 : RecordDataValid section14Catalog 8 (⟨222,(2),[8,12],[10],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1591 : RecordDataValid section14Catalog 8 (⟨222,(3),[3,4,8,12,15,16],[10],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1592 : RecordDataValid section14Catalog 8 (⟨222,(4),[3,4,7,8,12,15,16],[10],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1593 : RecordDataValid section14Catalog 8 (⟨222,(5),[3,4,8,12,15,16],[10],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1594 : RecordDataValid section14Catalog 8 (⟨222,(6),[4,8,12,16],[10],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1595 : RecordDataValid section14Catalog 8 (⟨222,(7),[8,12],[10],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1596 : RecordDataValid section14Catalog 8 (⟨222,(8),[3,4,8,12,15,16],[10],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1597 : RecordDataValid section14Catalog 8 (⟨222,(9),[3,4,7,8,12,15,16],[10],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1598 : RecordDataValid section14Catalog 8 (⟨222,(10),[4,8,12,16],[10],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1599 : RecordDataValid section14Catalog 8 (⟨222,(11),[4,8,12,16],[10],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1568).take 32 = [⟨221,(5),[4,8,12,16],[10],1353⟩,⟨221,(6),[4,8,12,16],[10],1353⟩,⟨221,(7),[4,8,12,16],[10],1354⟩,⟨221,(8),[4,8,12,16],[10],1355⟩,⟨221,(9),[4,8,12,16],[10],1356⟩,⟨221,(10),[4,8,12,16],[10],1357⟩,⟨221,(11),[4,8,12,16],[10],1357⟩,⟨221,(12),[4,8,12,16],[10],1358⟩,⟨221,(13),[4,8,12,16],[10],1355⟩,⟨221,(14),[4,8,12,16],[10],1356⟩,⟨221,(15),[4,8,12,16],[10],1359⟩,⟨221,(16),[4,8,12,16],[10],1359⟩,⟨221,(17),[4,8,12,16],[10],1359⟩,⟨221,(18),[4,8,16],[10],1355⟩,⟨221,(19),[4,8,12,16],[10],1359⟩,⟨221,(20),[4,8,12,16],[10],1360⟩,⟨221,(21),[4,8,12,16],[10],1360⟩,⟨221,(22),[4,8,12,16],[10],1360⟩,⟨221,(23),[4,8,12,16],[10],1355⟩,⟨221,(24),[8,12],[10],1360⟩,⟨222,(0),[4,8,12,16],[10],736⟩,⟨222,(1),[3,4,8,12,15,16],[10],736⟩,⟨222,(2),[8,12],[10],736⟩,⟨222,(3),[3,4,8,12,15,16],[10],736⟩,⟨222,(4),[3,4,7,8,12,15,16],[10],525⟩,⟨222,(5),[3,4,8,12,15,16],[10],735⟩,⟨222,(6),[4,8,12,16],[10],740⟩,⟨222,(7),[8,12],[10],740⟩,⟨222,(8),[3,4,8,12,15,16],[10],740⟩,⟨222,(9),[3,4,7,8,12,15,16],[10],528⟩,⟨222,(10),[4,8,12,16],[10],735⟩,⟨222,(11),[4,8,12,16],[10],738⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1568
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1569
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1570
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1571
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1572
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1573
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1574
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1575
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1576
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1577
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1578
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1579
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1580
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1581
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1582
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1583
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1584
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1585
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1586
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1587
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1588
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1589
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1590
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1591
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1592
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1593
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1594
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1595
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1596
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1597
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1598
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1599
end Section14Records_8_1568_1600

#print axioms solution
