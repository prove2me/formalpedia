-- Prove2me | solution 1 for Freiman.section14_s0009_records_1568_1600
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:49:35.673713+00:00
-- url     : https://prove2.me/submissions/acc179ee-bb0b-484c-8b40-abc35dafebae

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
namespace Section14Records_9_1568_1600
private theorem valid1568 : RecordDataValid section14Catalog 9 (⟨155,(18),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1569 : RecordDataValid section14Catalog 9 (⟨155,(19),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1570 : RecordDataValid section14Catalog 9 (⟨155,(20),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1571 : RecordDataValid section14Catalog 9 (⟨155,(21),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1572 : RecordDataValid section14Catalog 9 (⟨155,(22),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1573 : RecordDataValid section14Catalog 9 (⟨155,(23),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1574 : RecordDataValid section14Catalog 9 (⟨155,(24),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1575 : RecordDataValid section14Catalog 9 (⟨160,(0),[9,10],[42],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1576 : RecordDataValid section14Catalog 9 (⟨160,(1),[9,10],[42],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1577 : RecordDataValid section14Catalog 9 (⟨160,(2),[9,10],[42],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1578 : RecordDataValid section14Catalog 9 (⟨160,(3),[9,10],[42],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1579 : RecordDataValid section14Catalog 9 (⟨160,(4),[9,10],[42],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1580 : RecordDataValid section14Catalog 9 (⟨160,(5),[9,10],[42],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1581 : RecordDataValid section14Catalog 9 (⟨160,(6),[9,10],[42],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1582 : RecordDataValid section14Catalog 9 (⟨160,(7),[9,10],[42],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1583 : RecordDataValid section14Catalog 9 (⟨160,(8),[9,10],[42],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1584 : RecordDataValid section14Catalog 9 (⟨160,(9),[9,10],[42],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1585 : RecordDataValid section14Catalog 9 (⟨160,(10),[9,10],[42],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1586 : RecordDataValid section14Catalog 9 (⟨160,(11),[9,10],[42],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1587 : RecordDataValid section14Catalog 9 (⟨160,(12),[9,10],[42],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1588 : RecordDataValid section14Catalog 9 (⟨160,(13),[9,10],[42],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1589 : RecordDataValid section14Catalog 9 (⟨160,(14),[9,10],[42],643⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨643,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],644⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1590 : RecordDataValid section14Catalog 9 (⟨160,(15),[9,10],[42],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1591 : RecordDataValid section14Catalog 9 (⟨163,(0),[9],[42],1279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1279,[4,8,9,12,16],1283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1592 : RecordDataValid section14Catalog 9 (⟨163,(1),[9],[42],1280⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1280,[4,8,9,12,16],1284⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1593 : RecordDataValid section14Catalog 9 (⟨163,(2),[9],[42],1279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1279,[4,8,9,12,16],1283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1594 : RecordDataValid section14Catalog 9 (⟨163,(3),[9],[42],1281⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1281,[4,8,9,12,16],1285⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1595 : RecordDataValid section14Catalog 9 (⟨163,(4),[9],[42],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1596 : RecordDataValid section14Catalog 9 (⟨163,(5),[9],[42],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1597 : RecordDataValid section14Catalog 9 (⟨163,(6),[9],[42],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1598 : RecordDataValid section14Catalog 9 (⟨163,(7),[9],[42],1282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1282,[4,8,9,12,16],1286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1599 : RecordDataValid section14Catalog 9 (⟨163,(8),[9],[42],1283⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1283,[4,8,9,12,16],1287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1568).take 32 = [⟨155,(18),[9,10],[42],3⟩,⟨155,(19),[9,10],[42],3⟩,⟨155,(20),[9,10],[42],3⟩,⟨155,(21),[9,10],[42],3⟩,⟨155,(22),[9,10],[42],3⟩,⟨155,(23),[9,10],[42],3⟩,⟨155,(24),[9,10],[42],3⟩,⟨160,(0),[9,10],[42],638⟩,⟨160,(1),[9,10],[42],639⟩,⟨160,(2),[9,10],[42],640⟩,⟨160,(3),[9,10],[42],641⟩,⟨160,(4),[9,10],[42],638⟩,⟨160,(5),[9,10],[42],639⟩,⟨160,(6),[9,10],[42],642⟩,⟨160,(7),[9,10],[42],641⟩,⟨160,(8),[9,10],[42],638⟩,⟨160,(9),[9,10],[42],639⟩,⟨160,(10),[9,10],[42],640⟩,⟨160,(11),[9,10],[42],641⟩,⟨160,(12),[9,10],[42],638⟩,⟨160,(13),[9,10],[42],639⟩,⟨160,(14),[9,10],[42],643⟩,⟨160,(15),[9,10],[42],641⟩,⟨163,(0),[9],[42],1279⟩,⟨163,(1),[9],[42],1280⟩,⟨163,(2),[9],[42],1279⟩,⟨163,(3),[9],[42],1281⟩,⟨163,(4),[9],[42],1282⟩,⟨163,(5),[9],[42],1282⟩,⟨163,(6),[9],[42],1282⟩,⟨163,(7),[9],[42],1282⟩,⟨163,(8),[9],[42],1283⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1568
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1569
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1570
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1571
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1572
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1573
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1574
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1575
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1576
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1577
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1578
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1579
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1580
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1581
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1582
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1583
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1584
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1585
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1586
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1587
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1588
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1589
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1590
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1591
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1592
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1593
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1594
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1595
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1596
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1597
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1598
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1599
end Section14Records_9_1568_1600

#print axioms solution
