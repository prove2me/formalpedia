-- Prove2me | solution 1 for Freiman.section14_s0004_records_1632_1664
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:47:54.885969+00:00
-- url     : https://prove2.me/submissions/6bc00944-f09e-4964-ad7a-e1b32e14c155

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
namespace Section14Records_4_1632_1664
private theorem valid1632 : RecordDataValid section14Catalog 4 (⟨221,(10),[4,8,12,16],[10],1357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1357,[4,8,9,12,16],1361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1633 : RecordDataValid section14Catalog 4 (⟨221,(11),[4,8,12,16],[10],1357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1357,[4,8,9,12,16],1361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1634 : RecordDataValid section14Catalog 4 (⟨221,(12),[4,8,12,16],[10],1358⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1358,[4,8,9,12,16],1362⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1635 : RecordDataValid section14Catalog 4 (⟨221,(13),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1636 : RecordDataValid section14Catalog 4 (⟨221,(14),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1637 : RecordDataValid section14Catalog 4 (⟨221,(15),[4,8,12,16],[10],1359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1359,[4,8,9,12,16],1363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1638 : RecordDataValid section14Catalog 4 (⟨221,(16),[4,8,12,16],[10],1359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1359,[4,8,9,12,16],1363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1639 : RecordDataValid section14Catalog 4 (⟨221,(17),[4,8,12,16],[10],1359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1359,[4,8,9,12,16],1363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1640 : RecordDataValid section14Catalog 4 (⟨221,(18),[4,8,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1641 : RecordDataValid section14Catalog 4 (⟨221,(19),[4,8,12,16],[10],1359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1359,[4,8,9,12,16],1363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1642 : RecordDataValid section14Catalog 4 (⟨221,(20),[4,8,12,16],[10],1360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1360,[4,8,9,12,16],1364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1643 : RecordDataValid section14Catalog 4 (⟨221,(21),[4,8,12,16],[10],1360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1360,[4,8,9,12,16],1364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1644 : RecordDataValid section14Catalog 4 (⟨221,(22),[4,8,12,16],[10],1360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1360,[4,8,9,12,16],1364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1645 : RecordDataValid section14Catalog 4 (⟨221,(23),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1646 : RecordDataValid section14Catalog 4 (⟨221,(24),[4,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1647 : RecordDataValid section14Catalog 4 (⟨222,(0),[4,8,12,16],[10],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1648 : RecordDataValid section14Catalog 4 (⟨222,(1),[3,4,8,12,15,16],[10],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1649 : RecordDataValid section14Catalog 4 (⟨222,(2),[3,4,7,15,16],[10],737⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨737,[1,2,3,4,5,6,7,10,11,13,14,15,16],738⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1650 : RecordDataValid section14Catalog 4 (⟨222,(3),[3,4,8,12,15,16],[10],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1651 : RecordDataValid section14Catalog 4 (⟨222,(4),[3,4,7,8,12,15,16],[10],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1652 : RecordDataValid section14Catalog 4 (⟨222,(5),[3,4,8,12,15,16],[10],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1653 : RecordDataValid section14Catalog 4 (⟨222,(6),[4,8,12,16],[10],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1654 : RecordDataValid section14Catalog 4 (⟨222,(7),[3,4,7,15,16],[10],739⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨739,[1,2,3,4,5,6,7,10,11,13,14,15,16],740⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1655 : RecordDataValid section14Catalog 4 (⟨222,(8),[3,4,8,12,15,16],[10],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1656 : RecordDataValid section14Catalog 4 (⟨222,(9),[3,4,7,8,12,15,16],[10],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1657 : RecordDataValid section14Catalog 4 (⟨222,(10),[4,8,12,16],[10],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1658 : RecordDataValid section14Catalog 4 (⟨222,(11),[4,8,12,16],[10],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1659 : RecordDataValid section14Catalog 4 (⟨222,(12),[4,16],[10],1361⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1361,[4,5,10,16],1365⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1660 : RecordDataValid section14Catalog 4 (⟨222,(13),[4,8,12,16],[10],1362⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1362,[4,5,8,9,12,16],1366⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1661 : RecordDataValid section14Catalog 4 (⟨222,(14),[3,4,7,8,12,15,16],[10],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1662 : RecordDataValid section14Catalog 4 (⟨222,(15),[3,4,8,12,15,16],[10],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1663 : RecordDataValid section14Catalog 4 (⟨222,(16),[3,4,8,12,15,16],[10],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1632).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1632).take 32 = [⟨221,(10),[4,8,12,16],[10],1357⟩,⟨221,(11),[4,8,12,16],[10],1357⟩,⟨221,(12),[4,8,12,16],[10],1358⟩,⟨221,(13),[4,8,12,16],[10],1355⟩,⟨221,(14),[4,8,12,16],[10],1356⟩,⟨221,(15),[4,8,12,16],[10],1359⟩,⟨221,(16),[4,8,12,16],[10],1359⟩,⟨221,(17),[4,8,12,16],[10],1359⟩,⟨221,(18),[4,8,16],[10],1355⟩,⟨221,(19),[4,8,12,16],[10],1359⟩,⟨221,(20),[4,8,12,16],[10],1360⟩,⟨221,(21),[4,8,12,16],[10],1360⟩,⟨221,(22),[4,8,12,16],[10],1360⟩,⟨221,(23),[4,8,12,16],[10],1355⟩,⟨221,(24),[4,16],[10],1356⟩,⟨222,(0),[4,8,12,16],[10],736⟩,⟨222,(1),[3,4,8,12,15,16],[10],736⟩,⟨222,(2),[3,4,7,15,16],[10],737⟩,⟨222,(3),[3,4,8,12,15,16],[10],736⟩,⟨222,(4),[3,4,7,8,12,15,16],[10],525⟩,⟨222,(5),[3,4,8,12,15,16],[10],735⟩,⟨222,(6),[4,8,12,16],[10],740⟩,⟨222,(7),[3,4,7,15,16],[10],739⟩,⟨222,(8),[3,4,8,12,15,16],[10],740⟩,⟨222,(9),[3,4,7,8,12,15,16],[10],528⟩,⟨222,(10),[4,8,12,16],[10],735⟩,⟨222,(11),[4,8,12,16],[10],738⟩,⟨222,(12),[4,16],[10],1361⟩,⟨222,(13),[4,8,12,16],[10],1362⟩,⟨222,(14),[3,4,7,8,12,15,16],[10],531⟩,⟨222,(15),[3,4,8,12,15,16],[10],735⟩,⟨222,(16),[3,4,8,12,15,16],[10],738⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1632
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1633
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1634
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1635
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1636
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1637
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1638
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1639
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1640
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1641
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1642
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1643
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1644
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1645
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1646
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1647
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1648
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1649
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1650
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1651
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1652
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1653
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1654
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1655
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1656
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1657
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1658
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1659
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1660
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1661
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1662
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1663
end Section14Records_4_1632_1664

#print axioms solution
