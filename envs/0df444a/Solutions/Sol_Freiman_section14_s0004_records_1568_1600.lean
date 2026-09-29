-- Prove2me | solution 1 for Freiman.section14_s0004_records_1568_1600
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:46:08.132568+00:00
-- url     : https://prove2.me/submissions/cc8a0076-0a33-40af-ba7d-7dfa419495de

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
namespace Section14Records_4_1568_1600
private theorem valid1568 : RecordDataValid section14Catalog 4 (⟨213,(2),[4,8,12,16],[10],1343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1343,[4,8,9,12,16],1347⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1569 : RecordDataValid section14Catalog 4 (⟨213,(3),[4,8,12,16],[10],1345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1345,[4,8,9,12,16],1349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1570 : RecordDataValid section14Catalog 4 (⟨213,(4),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1571 : RecordDataValid section14Catalog 4 (⟨213,(5),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1572 : RecordDataValid section14Catalog 4 (⟨213,(6),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1573 : RecordDataValid section14Catalog 4 (⟨213,(7),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1574 : RecordDataValid section14Catalog 4 (⟨213,(8),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1575 : RecordDataValid section14Catalog 4 (⟨213,(9),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1576 : RecordDataValid section14Catalog 4 (⟨213,(10),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1577 : RecordDataValid section14Catalog 4 (⟨213,(11),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1578 : RecordDataValid section14Catalog 4 (⟨213,(12),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1579 : RecordDataValid section14Catalog 4 (⟨213,(13),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1580 : RecordDataValid section14Catalog 4 (⟨213,(14),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1581 : RecordDataValid section14Catalog 4 (⟨213,(15),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1582 : RecordDataValid section14Catalog 4 (⟨215,(0),[4,8,12],[10],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1583 : RecordDataValid section14Catalog 4 (⟨215,(1),[4,8,12],[10],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1584 : RecordDataValid section14Catalog 4 (⟨215,(2),[4,8,12],[10],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1585 : RecordDataValid section14Catalog 4 (⟨215,(3),[4,8,12],[10],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1586 : RecordDataValid section14Catalog 4 (⟨215,(4),[4,8,12],[10],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1587 : RecordDataValid section14Catalog 4 (⟨215,(5),[4,8,12],[10],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1588 : RecordDataValid section14Catalog 4 (⟨215,(6),[4,8,12],[10],732⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨732,[1,2,4,5,6,8,9,10,12],733⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1589 : RecordDataValid section14Catalog 4 (⟨215,(7),[4,8,12],[10],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1590 : RecordDataValid section14Catalog 4 (⟨215,(8),[4,8,12],[10],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1591 : RecordDataValid section14Catalog 4 (⟨215,(9),[4,8,12],[10],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1592 : RecordDataValid section14Catalog 4 (⟨215,(10),[4,8,12],[10],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1593 : RecordDataValid section14Catalog 4 (⟨215,(11),[4,8,12],[10],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1594 : RecordDataValid section14Catalog 4 (⟨215,(12),[4,8,12],[10],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1595 : RecordDataValid section14Catalog 4 (⟨215,(13),[4,8,12],[10],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1596 : RecordDataValid section14Catalog 4 (⟨215,(14),[4,8,12],[10],733⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨733,[1,2,4,5,6,8,9,10,12],734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1597 : RecordDataValid section14Catalog 4 (⟨215,(15),[4,8,12],[10],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1598 : RecordDataValid section14Catalog 4 (⟨218,(0),[4,8,12],[10],1349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1349,[4,8,9,12],1353⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1599 : RecordDataValid section14Catalog 4 (⟨218,(1),[4,8,12],[10],1350⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1350,[4,8,9,12],1354⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1568).take 32 = [⟨213,(2),[4,8,12,16],[10],1343⟩,⟨213,(3),[4,8,12,16],[10],1345⟩,⟨213,(4),[4,8,12,16],[10],1346⟩,⟨213,(5),[4,8,12,16],[10],1346⟩,⟨213,(6),[4,8,12,16],[10],1346⟩,⟨213,(7),[4,8,12,16],[10],1346⟩,⟨213,(8),[4,8,12,16],[10],1347⟩,⟨213,(9),[4,8,12,16],[10],1347⟩,⟨213,(10),[4,8,12,16],[10],1347⟩,⟨213,(11),[4,8,12,16],[10],1347⟩,⟨213,(12),[4,8,12,16],[10],1348⟩,⟨213,(13),[4,8,12,16],[10],1348⟩,⟨213,(14),[4,8,12,16],[10],1348⟩,⟨213,(15),[4,8,12,16],[10],1348⟩,⟨215,(0),[4,8,12],[10],728⟩,⟨215,(1),[4,8,12],[10],729⟩,⟨215,(2),[4,8,12],[10],730⟩,⟨215,(3),[4,8,12],[10],731⟩,⟨215,(4),[4,8,12],[10],728⟩,⟨215,(5),[4,8,12],[10],729⟩,⟨215,(6),[4,8,12],[10],732⟩,⟨215,(7),[4,8,12],[10],731⟩,⟨215,(8),[4,8,12],[10],728⟩,⟨215,(9),[4,8,12],[10],729⟩,⟨215,(10),[4,8,12],[10],730⟩,⟨215,(11),[4,8,12],[10],731⟩,⟨215,(12),[4,8,12],[10],728⟩,⟨215,(13),[4,8,12],[10],729⟩,⟨215,(14),[4,8,12],[10],733⟩,⟨215,(15),[4,8,12],[10],731⟩,⟨218,(0),[4,8,12],[10],1349⟩,⟨218,(1),[4,8,12],[10],1350⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1568
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1569
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1570
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1571
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1572
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1573
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1574
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1575
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1576
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1577
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1578
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1579
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1580
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1581
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1582
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1583
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1584
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1585
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1586
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1587
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1588
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1589
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1590
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1591
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1592
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1593
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1594
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1595
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1596
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1597
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1598
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1599
end Section14Records_4_1568_1600

#print axioms solution
