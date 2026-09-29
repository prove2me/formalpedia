-- Prove2me | solution 1 for Freiman.section14_s0008_records_1632_1664
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:34:23.533615+00:00
-- url     : https://prove2.me/submissions/6a23b6c5-395e-40f1-b5a8-20ffb42758f9

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
namespace Section14Records_8_1632_1664
private theorem valid1632 : RecordDataValid section14Catalog 8 (⟨224,(19),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1633 : RecordDataValid section14Catalog 8 (⟨224,(20),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1634 : RecordDataValid section14Catalog 8 (⟨224,(21),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1635 : RecordDataValid section14Catalog 8 (⟨224,(22),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1636 : RecordDataValid section14Catalog 8 (⟨224,(23),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1637 : RecordDataValid section14Catalog 8 (⟨224,(24),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1638 : RecordDataValid section14Catalog 8 (⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1639 : RecordDataValid section14Catalog 8 (⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1640 : RecordDataValid section14Catalog 8 (⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1641 : RecordDataValid section14Catalog 8 (⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1642 : RecordDataValid section14Catalog 8 (⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1643 : RecordDataValid section14Catalog 8 (⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1644 : RecordDataValid section14Catalog 8 (⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1645 : RecordDataValid section14Catalog 8 (⟨225,(7),[4,8,12,16],[10],1368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1368,[4,8,9,12,16],1372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1646 : RecordDataValid section14Catalog 8 (⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1647 : RecordDataValid section14Catalog 8 (⟨225,(9),[4,8,12,16],[10],1368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1368,[4,8,9,12,16],1372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1648 : RecordDataValid section14Catalog 8 (⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1649 : RecordDataValid section14Catalog 8 (⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1650 : RecordDataValid section14Catalog 8 (⟨225,(12),[4,8,12,16],[10],1369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1369,[4,8,9,12,16],1373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1651 : RecordDataValid section14Catalog 8 (⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1652 : RecordDataValid section14Catalog 8 (⟨225,(14),[4,8,12,16],[10],1369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1369,[4,8,9,12,16],1373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1653 : RecordDataValid section14Catalog 8 (⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1654 : RecordDataValid section14Catalog 8 (⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1655 : RecordDataValid section14Catalog 8 (⟨225,(17),[4,8,12,16],[10],1370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1370,[4,8,9,12,16],1374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1656 : RecordDataValid section14Catalog 8 (⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1657 : RecordDataValid section14Catalog 8 (⟨225,(19),[4,8,12,16],[10],1370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1370,[4,8,9,12,16],1374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1658 : RecordDataValid section14Catalog 8 (⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1659 : RecordDataValid section14Catalog 8 (⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1660 : RecordDataValid section14Catalog 8 (⟨225,(22),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1661 : RecordDataValid section14Catalog 8 (⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1662 : RecordDataValid section14Catalog 8 (⟨225,(24),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1663 : RecordDataValid section14Catalog 8 (⟨226,(0),[3,4,8,12,15,16],[10],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1632).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1632).take 32 = [⟨224,(19),[4,8,12,16],[10],1356⟩,⟨224,(20),[4,8,12,16],[10],1367⟩,⟨224,(21),[4,8,12,16],[10],1367⟩,⟨224,(22),[4,8,12,16],[10],1367⟩,⟨224,(23),[4,8,12,16],[10],1355⟩,⟨224,(24),[4,8,12,16],[10],1356⟩,⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩,⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩,⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩,⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩,⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩,⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩,⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩,⟨225,(7),[4,8,12,16],[10],1368⟩,⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩,⟨225,(9),[4,8,12,16],[10],1368⟩,⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩,⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩,⟨225,(12),[4,8,12,16],[10],1369⟩,⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩,⟨225,(14),[4,8,12,16],[10],1369⟩,⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩,⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩,⟨225,(17),[4,8,12,16],[10],1370⟩,⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩,⟨225,(19),[4,8,12,16],[10],1370⟩,⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩,⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩,⟨225,(22),[4,8,12,16],[10],1367⟩,⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩,⟨225,(24),[4,8,12,16],[10],1367⟩,⟨226,(0),[3,4,8,12,15,16],[10],766⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1632
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1633
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1634
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1635
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1636
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1637
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1638
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1639
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1640
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1641
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1642
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1643
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1644
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1645
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1646
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1647
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1648
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1649
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1650
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1651
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1652
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1653
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1654
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1655
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1656
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1657
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1658
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1659
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1660
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1661
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1662
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1663
end Section14Records_8_1632_1664

#print axioms solution
