-- Prove2me | solution 1 for Freiman.section14_s0009_records_2592_2624
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:37:05.673591+00:00
-- url     : https://prove2.me/submissions/400d7fb0-35bd-4615-ac88-149f40a7751c

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
namespace Section14Records_9_2592_2624
private theorem valid2592 : RecordDataValid section14Catalog 9 (⟨290,(0),[9],[42],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2593 : RecordDataValid section14Catalog 9 (⟨290,(1),[9],[42],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2594 : RecordDataValid section14Catalog 9 (⟨290,(2),[9],[42],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2595 : RecordDataValid section14Catalog 9 (⟨290,(3),[9],[42],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2596 : RecordDataValid section14Catalog 9 (⟨290,(4),[9],[42],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2597 : RecordDataValid section14Catalog 9 (⟨290,(5),[9],[42],1441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1441,[5,8,9,12],1446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2598 : RecordDataValid section14Catalog 9 (⟨290,(6),[9],[42],1441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1441,[5,8,9,12],1446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2599 : RecordDataValid section14Catalog 9 (⟨290,(7),[9],[42],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2600 : RecordDataValid section14Catalog 9 (⟨290,(8),[9],[42],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2601 : RecordDataValid section14Catalog 9 (⟨290,(9),[9],[42],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2602 : RecordDataValid section14Catalog 9 (⟨290,(10),[9],[42],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2603 : RecordDataValid section14Catalog 9 (⟨290,(11),[9],[42],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2604 : RecordDataValid section14Catalog 9 (⟨290,(12),[9],[42],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2605 : RecordDataValid section14Catalog 9 (⟨290,(13),[9],[42],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2606 : RecordDataValid section14Catalog 9 (⟨290,(14),[9],[42],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2607 : RecordDataValid section14Catalog 9 (⟨290,(15),[9],[42],1442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1442,[5,8,9,12],1447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2608 : RecordDataValid section14Catalog 9 (⟨290,(16),[9],[42],1442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1442,[5,8,9,12],1447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2609 : RecordDataValid section14Catalog 9 (⟨290,(17),[9],[42],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2610 : RecordDataValid section14Catalog 9 (⟨290,(18),[9],[42],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2611 : RecordDataValid section14Catalog 9 (⟨290,(19),[9],[42],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2612 : RecordDataValid section14Catalog 9 (⟨290,(20),[9],[42],1443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1443,[5,8,9,12],1448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2613 : RecordDataValid section14Catalog 9 (⟨290,(21),[9],[42],1443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1443,[5,8,9,12],1448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2614 : RecordDataValid section14Catalog 9 (⟨290,(22),[9],[42],1443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1443,[5,8,9,12],1448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2615 : RecordDataValid section14Catalog 9 (⟨290,(23),[9],[42],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2616 : RecordDataValid section14Catalog 9 (⟨290,(24),[9],[42],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2617 : RecordDataValid section14Catalog 9 (⟨293,(0),[9],[42],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2618 : RecordDataValid section14Catalog 9 (⟨293,(1),[9],[42],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2619 : RecordDataValid section14Catalog 9 (⟨293,(2),[9],[42],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2620 : RecordDataValid section14Catalog 9 (⟨293,(3),[9],[42],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2621 : RecordDataValid section14Catalog 9 (⟨293,(4),[9],[42],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2622 : RecordDataValid section14Catalog 9 (⟨293,(5),[9],[42],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2623 : RecordDataValid section14Catalog 9 (⟨293,(6),[9],[42],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2592).take 32 = [⟨290,(0),[9],[42],1437⟩,⟨290,(1),[9],[42],1437⟩,⟨290,(2),[9],[42],1438⟩,⟨290,(3),[9],[42],1439⟩,⟨290,(4),[9],[42],1440⟩,⟨290,(5),[9],[42],1441⟩,⟨290,(6),[9],[42],1441⟩,⟨290,(7),[9],[42],1438⟩,⟨290,(8),[9],[42],1439⟩,⟨290,(9),[9],[42],1440⟩,⟨290,(10),[9],[42],1437⟩,⟨290,(11),[9],[42],1437⟩,⟨290,(12),[9],[42],1438⟩,⟨290,(13),[9],[42],1439⟩,⟨290,(14),[9],[42],1440⟩,⟨290,(15),[9],[42],1442⟩,⟨290,(16),[9],[42],1442⟩,⟨290,(17),[9],[42],1438⟩,⟨290,(18),[9],[42],1439⟩,⟨290,(19),[9],[42],1440⟩,⟨290,(20),[9],[42],1443⟩,⟨290,(21),[9],[42],1443⟩,⟨290,(22),[9],[42],1443⟩,⟨290,(23),[9],[42],1439⟩,⟨290,(24),[9],[42],1440⟩,⟨293,(0),[9],[42],1152⟩,⟨293,(1),[9],[42],1153⟩,⟨293,(2),[9],[42],1154⟩,⟨293,(3),[9],[42],1154⟩,⟨293,(4),[9],[42],1154⟩,⟨293,(5),[9],[42],1152⟩,⟨293,(6),[9],[42],1153⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2592
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2593
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2594
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2595
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2596
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2597
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2598
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2599
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2600
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2601
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2602
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2603
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2604
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2605
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2606
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2607
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2608
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2609
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2610
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2611
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2612
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2613
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2614
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2615
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2616
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2617
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2618
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2619
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2620
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2621
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2622
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2623
end Section14Records_9_2592_2624

#print axioms solution
