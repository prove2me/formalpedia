-- Prove2me | solution 1 for Freiman.section14_s0015_records_0640_0672
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T18:58:58.089564+00:00
-- url     : https://prove2.me/submissions/88a26e5b-94a8-4d19-b80f-cb39b0e15ce2

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
namespace Section14Records_15_640_672
private theorem valid640 : RecordDataValid section14Catalog 15 (⟨190,(20),[3,4,8,12,15,16],[10],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid641 : RecordDataValid section14Catalog 15 (⟨190,(21),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid642 : RecordDataValid section14Catalog 15 (⟨190,(22),[3,4,8,12,15,16],[10],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid643 : RecordDataValid section14Catalog 15 (⟨190,(23),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid644 : RecordDataValid section14Catalog 15 (⟨190,(24),[3,4,8,12,15,16],[10],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid645 : RecordDataValid section14Catalog 15 (⟨192,(0),[3,7,15],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid646 : RecordDataValid section14Catalog 15 (⟨192,(1),[3,7,15],[10],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid647 : RecordDataValid section14Catalog 15 (⟨192,(2),[3,7,15],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid648 : RecordDataValid section14Catalog 15 (⟨192,(3),[3,7,15],[10],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid649 : RecordDataValid section14Catalog 15 (⟨192,(4),[3,7,15],[10],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid650 : RecordDataValid section14Catalog 15 (⟨192,(5),[3,7,15],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid651 : RecordDataValid section14Catalog 15 (⟨192,(6),[3,7,15],[10],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid652 : RecordDataValid section14Catalog 15 (⟨192,(7),[3,7,15],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid653 : RecordDataValid section14Catalog 15 (⟨192,(8),[3,7,15],[10],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid654 : RecordDataValid section14Catalog 15 (⟨192,(9),[3,7,15],[10],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid655 : RecordDataValid section14Catalog 15 (⟨192,(10),[3,7,15],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid656 : RecordDataValid section14Catalog 15 (⟨192,(11),[3,7,15],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid657 : RecordDataValid section14Catalog 15 (⟨192,(12),[3,7,15],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid658 : RecordDataValid section14Catalog 15 (⟨192,(13),[3,7,15],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid659 : RecordDataValid section14Catalog 15 (⟨192,(14),[3,7,15],[10],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid660 : RecordDataValid section14Catalog 15 (⟨192,(15),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid661 : RecordDataValid section14Catalog 15 (⟨192,(16),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid662 : RecordDataValid section14Catalog 15 (⟨192,(17),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid663 : RecordDataValid section14Catalog 15 (⟨192,(18),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid664 : RecordDataValid section14Catalog 15 (⟨192,(19),[3,7,15],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid665 : RecordDataValid section14Catalog 15 (⟨192,(20),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid666 : RecordDataValid section14Catalog 15 (⟨192,(21),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid667 : RecordDataValid section14Catalog 15 (⟨192,(22),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid668 : RecordDataValid section14Catalog 15 (⟨192,(23),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid669 : RecordDataValid section14Catalog 15 (⟨192,(24),[3,7,15],[10],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid670 : RecordDataValid section14Catalog 15 (⟨195,(0),[3,4,8,12,15,16],[10],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid671 : RecordDataValid section14Catalog 15 (⟨195,(1),[3,4,8,12,15,16],[10],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 640).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 640).take 32 = [⟨190,(20),[3,4,8,12,15,16],[10],692⟩,⟨190,(21),[3,4,8,12,15,16],[10],693⟩,⟨190,(22),[3,4,8,12,15,16],[10],694⟩,⟨190,(23),[3,4,8,12,15,16],[10],693⟩,⟨190,(24),[3,4,8,12,15,16],[10],695⟩,⟨192,(0),[3,7,15],[10],441⟩,⟨192,(1),[3,7,15],[10],442⟩,⟨192,(2),[3,7,15],[10],441⟩,⟨192,(3),[3,7,15],[10],443⟩,⟨192,(4),[3,7,15],[10],444⟩,⟨192,(5),[3,7,15],[10],441⟩,⟨192,(6),[3,7,15],[10],442⟩,⟨192,(7),[3,7,15],[10],441⟩,⟨192,(8),[3,7,15],[10],443⟩,⟨192,(9),[3,7,15],[10],444⟩,⟨192,(10),[3,7,15],[10],445⟩,⟨192,(11),[3,7,15],[10],445⟩,⟨192,(12),[3,7,15],[10],445⟩,⟨192,(13),[3,7,15],[10],445⟩,⟨192,(14),[3,7,15],[10],444⟩,⟨192,(15),[3,7,15],[10],446⟩,⟨192,(16),[3,7,15],[10],446⟩,⟨192,(17),[3,7,15],[10],446⟩,⟨192,(18),[3,7,15],[10],446⟩,⟨192,(19),[3,7,15],[10],446⟩,⟨192,(20),[3,7,15],[10],447⟩,⟨192,(21),[3,7,15],[10],447⟩,⟨192,(22),[3,7,15],[10],447⟩,⟨192,(23),[3,7,15],[10],447⟩,⟨192,(24),[3,7,15],[10],447⟩,⟨195,(0),[3,4,8,12,15,16],[10],697⟩,⟨195,(1),[3,4,8,12,15,16],[10],697⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid640
  · exact recordValid_of_data section14Catalog 15 _ hnum valid641
  · exact recordValid_of_data section14Catalog 15 _ hnum valid642
  · exact recordValid_of_data section14Catalog 15 _ hnum valid643
  · exact recordValid_of_data section14Catalog 15 _ hnum valid644
  · exact recordValid_of_data section14Catalog 15 _ hnum valid645
  · exact recordValid_of_data section14Catalog 15 _ hnum valid646
  · exact recordValid_of_data section14Catalog 15 _ hnum valid647
  · exact recordValid_of_data section14Catalog 15 _ hnum valid648
  · exact recordValid_of_data section14Catalog 15 _ hnum valid649
  · exact recordValid_of_data section14Catalog 15 _ hnum valid650
  · exact recordValid_of_data section14Catalog 15 _ hnum valid651
  · exact recordValid_of_data section14Catalog 15 _ hnum valid652
  · exact recordValid_of_data section14Catalog 15 _ hnum valid653
  · exact recordValid_of_data section14Catalog 15 _ hnum valid654
  · exact recordValid_of_data section14Catalog 15 _ hnum valid655
  · exact recordValid_of_data section14Catalog 15 _ hnum valid656
  · exact recordValid_of_data section14Catalog 15 _ hnum valid657
  · exact recordValid_of_data section14Catalog 15 _ hnum valid658
  · exact recordValid_of_data section14Catalog 15 _ hnum valid659
  · exact recordValid_of_data section14Catalog 15 _ hnum valid660
  · exact recordValid_of_data section14Catalog 15 _ hnum valid661
  · exact recordValid_of_data section14Catalog 15 _ hnum valid662
  · exact recordValid_of_data section14Catalog 15 _ hnum valid663
  · exact recordValid_of_data section14Catalog 15 _ hnum valid664
  · exact recordValid_of_data section14Catalog 15 _ hnum valid665
  · exact recordValid_of_data section14Catalog 15 _ hnum valid666
  · exact recordValid_of_data section14Catalog 15 _ hnum valid667
  · exact recordValid_of_data section14Catalog 15 _ hnum valid668
  · exact recordValid_of_data section14Catalog 15 _ hnum valid669
  · exact recordValid_of_data section14Catalog 15 _ hnum valid670
  · exact recordValid_of_data section14Catalog 15 _ hnum valid671
end Section14Records_15_640_672

#print axioms solution
