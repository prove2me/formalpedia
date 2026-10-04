-- Prove2me | solution 1 for Freiman.section14_s0013_records_1600_1632
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-21T08:25:15.208949+00:00
-- url     : https://prove2.me/submissions/6929de1d-007b-4e79-8e0c-576e70f1efd3

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
namespace Section14Records_13_1600_1632
private theorem valid1600 : RecordDataValid section14Catalog 13 (⟨111,(3),[1,5,6,13],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1601 : RecordDataValid section14Catalog 13 (⟨111,(4),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1602 : RecordDataValid section14Catalog 13 (⟨111,(5),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1603 : RecordDataValid section14Catalog 13 (⟨111,(6),[1,5,6,13],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1604 : RecordDataValid section14Catalog 13 (⟨111,(7),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1605 : RecordDataValid section14Catalog 13 (⟨111,(8),[1,5,6,13],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1606 : RecordDataValid section14Catalog 13 (⟨111,(9),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1607 : RecordDataValid section14Catalog 13 (⟨111,(10),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1608 : RecordDataValid section14Catalog 13 (⟨111,(11),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1609 : RecordDataValid section14Catalog 13 (⟨111,(12),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1610 : RecordDataValid section14Catalog 13 (⟨111,(13),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1611 : RecordDataValid section14Catalog 13 (⟨111,(14),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1612 : RecordDataValid section14Catalog 13 (⟨111,(15),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1613 : RecordDataValid section14Catalog 13 (⟨111,(16),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1614 : RecordDataValid section14Catalog 13 (⟨111,(17),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1615 : RecordDataValid section14Catalog 13 (⟨111,(18),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1616 : RecordDataValid section14Catalog 13 (⟨111,(19),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1617 : RecordDataValid section14Catalog 13 (⟨111,(20),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1618 : RecordDataValid section14Catalog 13 (⟨111,(21),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1619 : RecordDataValid section14Catalog 13 (⟨111,(22),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1620 : RecordDataValid section14Catalog 13 (⟨111,(23),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1621 : RecordDataValid section14Catalog 13 (⟨111,(24),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1622 : RecordDataValid section14Catalog 13 (⟨114,(0),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1623 : RecordDataValid section14Catalog 13 (⟨114,(1),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1624 : RecordDataValid section14Catalog 13 (⟨114,(2),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1625 : RecordDataValid section14Catalog 13 (⟨114,(3),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1626 : RecordDataValid section14Catalog 13 (⟨114,(4),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1627 : RecordDataValid section14Catalog 13 (⟨114,(5),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1628 : RecordDataValid section14Catalog 13 (⟨114,(6),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1629 : RecordDataValid section14Catalog 13 (⟨114,(7),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1630 : RecordDataValid section14Catalog 13 (⟨114,(8),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1631 : RecordDataValid section14Catalog 13 (⟨114,(9),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1600).take 32 = [⟨111,(3),[1,5,6,13],[170],455⟩,⟨111,(4),[1,5,6,13],[170],456⟩,⟨111,(5),[1,5,6,13],[170],453⟩,⟨111,(6),[1,5,6,13],[170],454⟩,⟨111,(7),[1,5,6,13],[170],453⟩,⟨111,(8),[1,5,6,13],[170],455⟩,⟨111,(9),[1,5,6,13],[170],456⟩,⟨111,(10),[1,5,6,13],[170],457⟩,⟨111,(11),[1,5,6,13],[170],457⟩,⟨111,(12),[1,5,6,13],[170],457⟩,⟨111,(13),[1,5,6,13],[170],457⟩,⟨111,(14),[1,5,6,13],[170],456⟩,⟨111,(15),[1,5,6,13],[170],458⟩,⟨111,(16),[1,5,6,13],[170],458⟩,⟨111,(17),[1,5,6,13],[170],458⟩,⟨111,(18),[1,5,6,13],[170],458⟩,⟨111,(19),[1,5,6,13],[170],458⟩,⟨111,(20),[1,5,6,13],[170],459⟩,⟨111,(21),[1,5,6,13],[170],459⟩,⟨111,(22),[1,5,6,13],[170],459⟩,⟨111,(23),[1,5,6,13],[170],459⟩,⟨111,(24),[1,5,6,13],[170],459⟩,⟨114,(0),[1,5,6,13],[170],460⟩,⟨114,(1),[1,5,6,13],[170],460⟩,⟨114,(2),[1,5,6,13],[170],460⟩,⟨114,(3),[1,5,6,13],[170],460⟩,⟨114,(4),[1,5,6,13],[170],460⟩,⟨114,(5),[1,5,6,13],[170],461⟩,⟨114,(6),[1,5,6,13],[170],461⟩,⟨114,(7),[1,5,6,13],[170],461⟩,⟨114,(8),[1,5,6,13],[170],461⟩,⟨114,(9),[1,5,6,13],[170],461⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1600
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1601
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1602
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1603
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1604
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1605
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1606
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1607
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1608
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1609
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1610
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1611
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1612
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1613
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1614
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1615
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1616
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1617
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1618
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1619
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1620
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1621
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1622
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1623
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1624
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1625
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1626
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1627
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1628
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1629
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1630
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1631
end Section14Records_13_1600_1632

#print axioms solution
