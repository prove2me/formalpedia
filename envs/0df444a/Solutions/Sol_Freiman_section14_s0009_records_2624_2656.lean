-- Prove2me | solution 1 for Freiman.section14_s0009_records_2624_2656
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:41:00.072375+00:00
-- url     : https://prove2.me/submissions/9f4c83b3-1f98-4ee4-82b2-2ea4bd649826

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
namespace Section14Records_9_2624_2656
private theorem valid2624 : RecordDataValid section14Catalog 9 (⟨293,(7),[9],[42],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2625 : RecordDataValid section14Catalog 9 (⟨293,(8),[9],[42],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2626 : RecordDataValid section14Catalog 9 (⟨293,(9),[9],[42],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2627 : RecordDataValid section14Catalog 9 (⟨293,(10),[9],[42],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2628 : RecordDataValid section14Catalog 9 (⟨293,(11),[9],[42],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2629 : RecordDataValid section14Catalog 9 (⟨293,(12),[9],[42],1157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1157,[3,5,7,8,9,11,12,15],1161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2630 : RecordDataValid section14Catalog 9 (⟨293,(13),[9],[42],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2631 : RecordDataValid section14Catalog 9 (⟨293,(14),[9],[42],1157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1157,[3,5,7,8,9,11,12,15],1161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2632 : RecordDataValid section14Catalog 9 (⟨293,(15),[9],[42],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2633 : RecordDataValid section14Catalog 9 (⟨293,(16),[9],[42],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2634 : RecordDataValid section14Catalog 9 (⟨293,(17),[9],[42],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2635 : RecordDataValid section14Catalog 9 (⟨293,(18),[9],[42],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2636 : RecordDataValid section14Catalog 9 (⟨293,(19),[9],[42],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2637 : RecordDataValid section14Catalog 9 (⟨293,(20),[9],[42],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2638 : RecordDataValid section14Catalog 9 (⟨293,(21),[9],[42],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2639 : RecordDataValid section14Catalog 9 (⟨293,(22),[9],[42],1158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1158,[3,5,7,8,9,11,12,15],1162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2640 : RecordDataValid section14Catalog 9 (⟨293,(23),[9],[42],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2641 : RecordDataValid section14Catalog 9 (⟨293,(24),[9],[42],1158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1158,[3,5,7,8,9,11,12,15],1162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2642 : RecordDataValid section14Catalog 9 (⟨295,(0),[9],[42],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2643 : RecordDataValid section14Catalog 9 (⟨295,(1),[9],[42],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2644 : RecordDataValid section14Catalog 9 (⟨295,(2),[9],[42],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2645 : RecordDataValid section14Catalog 9 (⟨295,(3),[9],[42],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2646 : RecordDataValid section14Catalog 9 (⟨295,(4),[9],[42],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2647 : RecordDataValid section14Catalog 9 (⟨295,(5),[9],[42],1448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1448,[5,8,9,12],1453⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2648 : RecordDataValid section14Catalog 9 (⟨295,(6),[9],[42],1448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1448,[5,8,9,12],1453⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2649 : RecordDataValid section14Catalog 9 (⟨295,(7),[9],[42],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2650 : RecordDataValid section14Catalog 9 (⟨295,(8),[9],[42],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2651 : RecordDataValid section14Catalog 9 (⟨295,(9),[9],[42],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2652 : RecordDataValid section14Catalog 9 (⟨295,(10),[9],[42],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2653 : RecordDataValid section14Catalog 9 (⟨295,(11),[9],[42],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2654 : RecordDataValid section14Catalog 9 (⟨295,(12),[9],[42],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2655 : RecordDataValid section14Catalog 9 (⟨295,(13),[9],[42],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2624).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2624).take 32 = [⟨293,(7),[9],[42],1155⟩,⟨293,(8),[9],[42],1156⟩,⟨293,(9),[9],[42],1155⟩,⟨293,(10),[9],[42],1152⟩,⟨293,(11),[9],[42],1153⟩,⟨293,(12),[9],[42],1157⟩,⟨293,(13),[9],[42],1156⟩,⟨293,(14),[9],[42],1157⟩,⟨293,(15),[9],[42],1152⟩,⟨293,(16),[9],[42],1153⟩,⟨293,(17),[9],[42],1155⟩,⟨293,(18),[9],[42],1156⟩,⟨293,(19),[9],[42],1155⟩,⟨293,(20),[9],[42],1152⟩,⟨293,(21),[9],[42],1153⟩,⟨293,(22),[9],[42],1158⟩,⟨293,(23),[9],[42],1156⟩,⟨293,(24),[9],[42],1158⟩,⟨295,(0),[9],[42],1444⟩,⟨295,(1),[9],[42],1444⟩,⟨295,(2),[9],[42],1445⟩,⟨295,(3),[9],[42],1446⟩,⟨295,(4),[9],[42],1447⟩,⟨295,(5),[9],[42],1448⟩,⟨295,(6),[9],[42],1448⟩,⟨295,(7),[9],[42],1445⟩,⟨295,(8),[9],[42],1446⟩,⟨295,(9),[9],[42],1447⟩,⟨295,(10),[9],[42],1444⟩,⟨295,(11),[9],[42],1444⟩,⟨295,(12),[9],[42],1445⟩,⟨295,(13),[9],[42],1446⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2624
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2625
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2626
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2627
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2628
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2629
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2630
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2631
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2632
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2633
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2634
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2635
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2636
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2637
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2638
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2639
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2640
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2641
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2642
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2643
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2644
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2645
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2646
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2647
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2648
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2649
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2650
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2651
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2652
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2653
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2654
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2655
end Section14Records_9_2624_2656

#print axioms solution
