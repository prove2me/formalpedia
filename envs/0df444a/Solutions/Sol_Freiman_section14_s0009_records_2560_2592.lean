-- Prove2me | solution 1 for Freiman.section14_s0009_records_2560_2592
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:36:19.279345+00:00
-- url     : https://prove2.me/submissions/304e2815-d7fd-48f2-a878-6b45b9a53bd5

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
namespace Section14Records_9_2560_2592
private theorem valid2560 : RecordDataValid section14Catalog 9 (⟨285,(18),[9],[42],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2561 : RecordDataValid section14Catalog 9 (⟨285,(19),[9],[42],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2562 : RecordDataValid section14Catalog 9 (⟨285,(20),[9],[42],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2563 : RecordDataValid section14Catalog 9 (⟨285,(21),[9],[42],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2564 : RecordDataValid section14Catalog 9 (⟨285,(22),[9],[42],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2565 : RecordDataValid section14Catalog 9 (⟨285,(23),[9],[42],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2566 : RecordDataValid section14Catalog 9 (⟨285,(24),[9],[42],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2567 : RecordDataValid section14Catalog 9 (⟨288,(0),[9],[42],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2568 : RecordDataValid section14Catalog 9 (⟨288,(1),[9],[42],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2569 : RecordDataValid section14Catalog 9 (⟨288,(2),[9],[42],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2570 : RecordDataValid section14Catalog 9 (⟨288,(3),[9],[42],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2571 : RecordDataValid section14Catalog 9 (⟨288,(4),[9],[42],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2572 : RecordDataValid section14Catalog 9 (⟨288,(5),[9],[42],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2573 : RecordDataValid section14Catalog 9 (⟨288,(6),[9],[42],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2574 : RecordDataValid section14Catalog 9 (⟨288,(7),[9],[42],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2575 : RecordDataValid section14Catalog 9 (⟨288,(8),[9],[42],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2576 : RecordDataValid section14Catalog 9 (⟨288,(9),[9],[42],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2577 : RecordDataValid section14Catalog 9 (⟨288,(10),[9],[42],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2578 : RecordDataValid section14Catalog 9 (⟨288,(11),[9],[42],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2579 : RecordDataValid section14Catalog 9 (⟨288,(12),[9],[42],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2580 : RecordDataValid section14Catalog 9 (⟨288,(13),[9],[42],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2581 : RecordDataValid section14Catalog 9 (⟨288,(14),[9],[42],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2582 : RecordDataValid section14Catalog 9 (⟨288,(15),[9],[42],1140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1140,[3,5,7,8,9,11,12,15],1144⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2583 : RecordDataValid section14Catalog 9 (⟨288,(16),[9],[42],1141⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1141,[3,5,7,8,9,11,12,15],1145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2584 : RecordDataValid section14Catalog 9 (⟨288,(17),[9],[42],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2585 : RecordDataValid section14Catalog 9 (⟨288,(18),[9],[42],1143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1143,[3,5,7,8,9,11,12,15],1147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2586 : RecordDataValid section14Catalog 9 (⟨288,(19),[9],[42],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2587 : RecordDataValid section14Catalog 9 (⟨288,(20),[9],[42],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2588 : RecordDataValid section14Catalog 9 (⟨288,(21),[9],[42],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2589 : RecordDataValid section14Catalog 9 (⟨288,(22),[9],[42],1144⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1144,[3,5,7,8,9,11,12,15],1148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2590 : RecordDataValid section14Catalog 9 (⟨288,(23),[9],[42],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2591 : RecordDataValid section14Catalog 9 (⟨288,(24),[9],[42],1144⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1144,[3,5,7,8,9,11,12,15],1148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2560).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2560).take 32 = [⟨285,(18),[9],[42],1432⟩,⟨285,(19),[9],[42],1433⟩,⟨285,(20),[9],[42],1436⟩,⟨285,(21),[9],[42],1436⟩,⟨285,(22),[9],[42],1436⟩,⟨285,(23),[9],[42],1432⟩,⟨285,(24),[9],[42],1433⟩,⟨288,(0),[9],[42],1134⟩,⟨288,(1),[9],[42],1135⟩,⟨288,(2),[9],[42],1136⟩,⟨288,(3),[9],[42],1136⟩,⟨288,(4),[9],[42],1136⟩,⟨288,(5),[9],[42],1134⟩,⟨288,(6),[9],[42],1135⟩,⟨288,(7),[9],[42],1137⟩,⟨288,(8),[9],[42],1138⟩,⟨288,(9),[9],[42],1137⟩,⟨288,(10),[9],[42],1134⟩,⟨288,(11),[9],[42],1135⟩,⟨288,(12),[9],[42],1139⟩,⟨288,(13),[9],[42],1138⟩,⟨288,(14),[9],[42],1139⟩,⟨288,(15),[9],[42],1140⟩,⟨288,(16),[9],[42],1141⟩,⟨288,(17),[9],[42],1142⟩,⟨288,(18),[9],[42],1143⟩,⟨288,(19),[9],[42],1142⟩,⟨288,(20),[9],[42],1134⟩,⟨288,(21),[9],[42],1135⟩,⟨288,(22),[9],[42],1144⟩,⟨288,(23),[9],[42],1138⟩,⟨288,(24),[9],[42],1144⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2560
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2561
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2562
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2563
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2564
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2565
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2566
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2567
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2568
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2569
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2570
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2571
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2572
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2573
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2574
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2575
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2576
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2577
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2578
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2579
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2580
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2581
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2582
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2583
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2584
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2585
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2586
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2587
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2588
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2589
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2590
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2591
end Section14Records_9_2560_2592

#print axioms solution
