-- Prove2me | solution 1 for Freiman.section14_s0012_records_1600_1632
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:02:36.658982+00:00
-- url     : https://prove2.me/submissions/5821edb5-eee4-4139-afa7-9ade5d607026

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
namespace Section14Records_12_1600_1632
private theorem valid1600 : RecordDataValid section14Catalog 12 (⟨230,(4),[3,4,7,8,12,15,16],[10],814⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨814,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],815⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1601 : RecordDataValid section14Catalog 12 (⟨230,(5),[3,4,7,8,12,15,16],[10],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1602 : RecordDataValid section14Catalog 12 (⟨230,(6),[12],[10],1715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1715,[12],1720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1603 : RecordDataValid section14Catalog 12 (⟨230,(7),[4,8,12,16],[10],815⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨815,[1,4,5,6,8,9,10,12,13,16],816⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1604 : RecordDataValid section14Catalog 12 (⟨230,(8),[3,4,7,8,12,15,16],[10],816⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1605 : RecordDataValid section14Catalog 12 (⟨230,(9),[4,8,12,16],[10],1375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1375,[4,5,8,9,12,16],1379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1606 : RecordDataValid section14Catalog 12 (⟨230,(10),[3,4,7,8,12,15,16],[10],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1607 : RecordDataValid section14Catalog 12 (⟨230,(11),[3,4,7,8,12,15,16],[10],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1608 : RecordDataValid section14Catalog 12 (⟨230,(12),[4,8,12,16],[10],820⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨820,[1,4,5,8,9,10,12,13,16],821⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1609 : RecordDataValid section14Catalog 12 (⟨230,(13),[3,4,7,8,12,15,16],[10],821⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨821,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],822⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1610 : RecordDataValid section14Catalog 12 (⟨230,(14),[4,8,12,16],[10],1375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1375,[4,5,8,9,12,16],1379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1611 : RecordDataValid section14Catalog 12 (⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1612 : RecordDataValid section14Catalog 12 (⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1613 : RecordDataValid section14Catalog 12 (⟨230,(17),[4,8,12,16],[10],1376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1376,[4,8,9,12,16],1380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1614 : RecordDataValid section14Catalog 12 (⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨825,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],826⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1615 : RecordDataValid section14Catalog 12 (⟨230,(19),[4,8,12,16],[10],1376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1376,[4,8,9,12,16],1380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1616 : RecordDataValid section14Catalog 12 (⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1617 : RecordDataValid section14Catalog 12 (⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1618 : RecordDataValid section14Catalog 12 (⟨230,(22),[4,8,12,16],[10],1377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1377,[4,8,9,12,16],1381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1619 : RecordDataValid section14Catalog 12 (⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1620 : RecordDataValid section14Catalog 12 (⟨230,(24),[4,8,12,16],[10],1377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1377,[4,8,9,12,16],1381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1621 : RecordDataValid section14Catalog 12 (⟨231,(0),[3,4,8,12,15,16],[10],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1622 : RecordDataValid section14Catalog 12 (⟨231,(1),[8,12],[10],1646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1646,[8,9,12],1651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1623 : RecordDataValid section14Catalog 12 (⟨231,(2),[3,4,7,8,12,15,16],[10],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1624 : RecordDataValid section14Catalog 12 (⟨231,(3),[3,4,7,8,12,15,16],[10],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1625 : RecordDataValid section14Catalog 12 (⟨231,(4),[3,4,8,12,15,16],[10],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1626 : RecordDataValid section14Catalog 12 (⟨231,(5),[8,12],[10],1646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1646,[8,9,12],1651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1627 : RecordDataValid section14Catalog 12 (⟨231,(6),[3,4,7,8,12,15,16],[10],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1628 : RecordDataValid section14Catalog 12 (⟨231,(7),[3,4,7,8,12,15,16],[10],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1629 : RecordDataValid section14Catalog 12 (⟨231,(8),[3,4,7,8,12,15,16],[10],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1630 : RecordDataValid section14Catalog 12 (⟨231,(9),[3,4,7,8,12,15,16],[10],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1631 : RecordDataValid section14Catalog 12 (⟨231,(10),[3,4,7,8,12,15,16],[10],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1600).take 32 = [⟨230,(4),[3,4,7,8,12,15,16],[10],814⟩,⟨230,(5),[3,4,7,8,12,15,16],[10],810⟩,⟨230,(6),[12],[10],1715⟩,⟨230,(7),[4,8,12,16],[10],815⟩,⟨230,(8),[3,4,7,8,12,15,16],[10],816⟩,⟨230,(9),[4,8,12,16],[10],1375⟩,⟨230,(10),[3,4,7,8,12,15,16],[10],818⟩,⟨230,(11),[3,4,7,8,12,15,16],[10],819⟩,⟨230,(12),[4,8,12,16],[10],820⟩,⟨230,(13),[3,4,7,8,12,15,16],[10],821⟩,⟨230,(14),[4,8,12,16],[10],1375⟩,⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩,⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩,⟨230,(17),[4,8,12,16],[10],1376⟩,⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩,⟨230,(19),[4,8,12,16],[10],1376⟩,⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩,⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩,⟨230,(22),[4,8,12,16],[10],1377⟩,⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩,⟨230,(24),[4,8,12,16],[10],1377⟩,⟨231,(0),[3,4,8,12,15,16],[10],830⟩,⟨231,(1),[8,12],[10],1646⟩,⟨231,(2),[3,4,7,8,12,15,16],[10],832⟩,⟨231,(3),[3,4,7,8,12,15,16],[10],833⟩,⟨231,(4),[3,4,8,12,15,16],[10],830⟩,⟨231,(5),[8,12],[10],1646⟩,⟨231,(6),[3,4,7,8,12,15,16],[10],832⟩,⟨231,(7),[3,4,7,8,12,15,16],[10],833⟩,⟨231,(8),[3,4,7,8,12,15,16],[10],834⟩,⟨231,(9),[3,4,7,8,12,15,16],[10],835⟩,⟨231,(10),[3,4,7,8,12,15,16],[10],836⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1600
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1601
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1602
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1603
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1604
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1605
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1606
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1607
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1608
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1609
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1610
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1611
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1612
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1613
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1614
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1615
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1616
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1617
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1618
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1619
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1620
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1621
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1622
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1623
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1624
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1625
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1626
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1627
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1628
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1629
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1630
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1631
end Section14Records_12_1600_1632

#print axioms solution
