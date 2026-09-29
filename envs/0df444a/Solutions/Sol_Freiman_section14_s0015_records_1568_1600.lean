-- Prove2me | solution 1 for Freiman.section14_s0015_records_1568_1600
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:30:41.421807+00:00
-- url     : https://prove2.me/submissions/795f8e70-9342-47d8-8cef-255819ffc7e6

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
namespace Section14Records_15_1568_1600
private theorem valid1568 : RecordDataValid section14Catalog 15 (⟨465,(0),[3,7,15],[10],1197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1197,[3,7,11,15],1201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1569 : RecordDataValid section14Catalog 15 (⟨465,(1),[3,7,15],[10],1198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1198,[3,7,11,15],1202⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1570 : RecordDataValid section14Catalog 15 (⟨465,(2),[3,7,15],[10],1197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1197,[3,7,11,15],1201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1571 : RecordDataValid section14Catalog 15 (⟨465,(3),[3,7,15],[10],1199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1199,[3,7,11,15],1203⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1572 : RecordDataValid section14Catalog 15 (⟨466,(0),[3,7,15],[10],1200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1200,[3,5,7,8,9,11,12,15],1204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1573 : RecordDataValid section14Catalog 15 (⟨466,(1),[3,7,15],[10],1201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1201,[3,5,7,8,9,11,12,15],1205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1574 : RecordDataValid section14Catalog 15 (⟨466,(2),[3,7,15],[10],1202⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1202,[3,5,7,8,9,11,12,15],1206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1575 : RecordDataValid section14Catalog 15 (⟨466,(3),[3,7,15],[10],1203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1203,[3,5,7,8,9,11,15],1207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1576 : RecordDataValid section14Catalog 15 (⟨468,(0),[3,7,15],[10],1204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1204,[3,7,11,15],1208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1577 : RecordDataValid section14Catalog 15 (⟨468,(1),[3,7,15],[10],1205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1205,[3,7,11,15],1209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1578 : RecordDataValid section14Catalog 15 (⟨468,(2),[3,7,15],[10],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1579 : RecordDataValid section14Catalog 15 (⟨468,(3),[3,7,15],[10],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1580 : RecordDataValid section14Catalog 15 (⟨468,(4),[3,7,15],[10],1208⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1208,[3,7,11,15],1212⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1581 : RecordDataValid section14Catalog 15 (⟨468,(5),[3,7,15],[10],1205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1205,[3,7,11,15],1209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1582 : RecordDataValid section14Catalog 15 (⟨468,(6),[3,7,15],[10],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1583 : RecordDataValid section14Catalog 15 (⟨468,(7),[3,7,15],[10],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1584 : RecordDataValid section14Catalog 15 (⟨468,(8),[3,7,15],[10],1204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1204,[3,7,11,15],1208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1585 : RecordDataValid section14Catalog 15 (⟨468,(9),[3,7,15],[10],1209⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1209,[3,7,11,15],1213⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1586 : RecordDataValid section14Catalog 15 (⟨468,(10),[3,7,15],[10],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1587 : RecordDataValid section14Catalog 15 (⟨468,(11),[3,7,15],[10],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1588 : RecordDataValid section14Catalog 15 (⟨468,(12),[3,7,15],[10],1210⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1210,[3,7,11,15],1214⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1589 : RecordDataValid section14Catalog 15 (⟨468,(13),[3,7,15],[10],1205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1205,[3,7,11,15],1209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1590 : RecordDataValid section14Catalog 15 (⟨468,(14),[3,7,15],[10],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1591 : RecordDataValid section14Catalog 15 (⟨468,(15),[3,7,15],[10],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1592 : RecordDataValid section14Catalog 15 (⟨470,(0),[3,7,15],[10],1211⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1211,[3,5,7,8,9,11,12,15],1215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1593 : RecordDataValid section14Catalog 15 (⟨470,(1),[3,7,15],[10],1212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1212,[3,5,7,8,9,11,12,15],1216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1594 : RecordDataValid section14Catalog 15 (⟨470,(2),[3,7,15],[10],1213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1213,[3,5,7,8,9,11,12,15],1217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1595 : RecordDataValid section14Catalog 15 (⟨470,(3),[3,7,15],[10],1214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1214,[3,5,7,8,9,11,12,15],1218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1596 : RecordDataValid section14Catalog 15 (⟨470,(4),[3,7,15],[10],1215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1215,[3,5,7,8,9,11,12,15],1219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1597 : RecordDataValid section14Catalog 15 (⟨470,(5),[3,7,15],[10],1216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1216,[3,5,7,8,9,11,12,15],1220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1598 : RecordDataValid section14Catalog 15 (⟨470,(6),[3,7,15],[10],1217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1217,[3,5,7,8,9,11,12,15],1221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1599 : RecordDataValid section14Catalog 15 (⟨470,(7),[3,7,15],[10],1218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1218,[3,5,7,8,9,11,12,15],1222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1568).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1568).take 32 = [⟨465,(0),[3,7,15],[10],1197⟩,⟨465,(1),[3,7,15],[10],1198⟩,⟨465,(2),[3,7,15],[10],1197⟩,⟨465,(3),[3,7,15],[10],1199⟩,⟨466,(0),[3,7,15],[10],1200⟩,⟨466,(1),[3,7,15],[10],1201⟩,⟨466,(2),[3,7,15],[10],1202⟩,⟨466,(3),[3,7,15],[10],1203⟩,⟨468,(0),[3,7,15],[10],1204⟩,⟨468,(1),[3,7,15],[10],1205⟩,⟨468,(2),[3,7,15],[10],1206⟩,⟨468,(3),[3,7,15],[10],1207⟩,⟨468,(4),[3,7,15],[10],1208⟩,⟨468,(5),[3,7,15],[10],1205⟩,⟨468,(6),[3,7,15],[10],1206⟩,⟨468,(7),[3,7,15],[10],1207⟩,⟨468,(8),[3,7,15],[10],1204⟩,⟨468,(9),[3,7,15],[10],1209⟩,⟨468,(10),[3,7,15],[10],1206⟩,⟨468,(11),[3,7,15],[10],1207⟩,⟨468,(12),[3,7,15],[10],1210⟩,⟨468,(13),[3,7,15],[10],1205⟩,⟨468,(14),[3,7,15],[10],1206⟩,⟨468,(15),[3,7,15],[10],1207⟩,⟨470,(0),[3,7,15],[10],1211⟩,⟨470,(1),[3,7,15],[10],1212⟩,⟨470,(2),[3,7,15],[10],1213⟩,⟨470,(3),[3,7,15],[10],1214⟩,⟨470,(4),[3,7,15],[10],1215⟩,⟨470,(5),[3,7,15],[10],1216⟩,⟨470,(6),[3,7,15],[10],1217⟩,⟨470,(7),[3,7,15],[10],1218⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1568
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1569
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1570
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1571
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1572
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1573
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1574
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1575
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1576
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1577
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1578
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1579
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1580
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1581
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1582
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1583
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1584
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1585
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1586
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1587
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1588
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1589
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1590
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1591
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1592
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1593
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1594
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1595
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1596
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1597
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1598
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1599
end Section14Records_15_1568_1600

#print axioms solution
