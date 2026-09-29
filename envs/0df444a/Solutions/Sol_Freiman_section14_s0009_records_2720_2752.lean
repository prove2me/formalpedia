-- Prove2me | solution 1 for Freiman.section14_s0009_records_2720_2752
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:44:39.048383+00:00
-- url     : https://prove2.me/submissions/fa6acd26-76a8-46e1-9998-68b3c3ffbece

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
namespace Section14Records_9_2720_2752
private theorem valid2720 : RecordDataValid section14Catalog 9 (⟨307,(1),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2721 : RecordDataValid section14Catalog 9 (⟨307,(2),[9],[42],1473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1473,[5,9],1478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2722 : RecordDataValid section14Catalog 9 (⟨307,(3),[9],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2723 : RecordDataValid section14Catalog 9 (⟨307,(4),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2724 : RecordDataValid section14Catalog 9 (⟨307,(5),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2725 : RecordDataValid section14Catalog 9 (⟨307,(6),[9],[42],511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨511,[1,2,5,6,9,10,13,14],512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2726 : RecordDataValid section14Catalog 9 (⟨307,(7),[9],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2727 : RecordDataValid section14Catalog 9 (⟨307,(8),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2728 : RecordDataValid section14Catalog 9 (⟨307,(9),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2729 : RecordDataValid section14Catalog 9 (⟨307,(10),[9],[42],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2730 : RecordDataValid section14Catalog 9 (⟨307,(11),[9],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2731 : RecordDataValid section14Catalog 9 (⟨307,(12),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2732 : RecordDataValid section14Catalog 9 (⟨307,(13),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2733 : RecordDataValid section14Catalog 9 (⟨307,(14),[9],[42],513⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨513,[1,2,5,6,9,10,13,14],514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2734 : RecordDataValid section14Catalog 9 (⟨307,(15),[9],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2735 : RecordDataValid section14Catalog 9 (⟨307,(16),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2736 : RecordDataValid section14Catalog 9 (⟨307,(17),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2737 : RecordDataValid section14Catalog 9 (⟨307,(18),[9],[42],514⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨514,[1,2,4,5,6,8,9,10,12,13,14,16],515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2738 : RecordDataValid section14Catalog 9 (⟨307,(19),[9],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2739 : RecordDataValid section14Catalog 9 (⟨308,(8),[9],[42],1474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1474,[5,8,9,12],1479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2740 : RecordDataValid section14Catalog 9 (⟨308,(9),[9],[42],1475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1475,[5,8,9,12],1480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2741 : RecordDataValid section14Catalog 9 (⟨308,(10),[9],[42],1474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1474,[5,8,9,12],1479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2742 : RecordDataValid section14Catalog 9 (⟨308,(11),[9],[42],1476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1476,[5,8,9,12],1481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2743 : RecordDataValid section14Catalog 9 (⟨309,(0),[9],[42],1188⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1188,[3,5,7,8,9,11,12,15],1192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2744 : RecordDataValid section14Catalog 9 (⟨309,(1),[9],[42],1189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1189,[3,5,7,8,9,11,12,15],1193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2745 : RecordDataValid section14Catalog 9 (⟨309,(2),[9],[42],1190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1190,[3,5,7,8,9,11,12,15],1194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2746 : RecordDataValid section14Catalog 9 (⟨309,(3),[9],[42],1191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1191,[3,5,7,8,9,11,12,15],1195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2747 : RecordDataValid section14Catalog 9 (⟨309,(4),[9],[42],1477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1477,[5,9],1482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2748 : RecordDataValid section14Catalog 9 (⟨311,(0),[9],[42],1478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1478,[5,8,9,12],1483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2749 : RecordDataValid section14Catalog 9 (⟨311,(1),[9],[42],1479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1479,[5,8,9,12],1484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2750 : RecordDataValid section14Catalog 9 (⟨311,(2),[9],[42],1480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1480,[5,8,9,12],1485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2751 : RecordDataValid section14Catalog 9 (⟨311,(3),[9],[42],1481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1481,[5,8,9,12],1486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2720).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2720).take 32 = [⟨307,(1),[9],[42],3⟩,⟨307,(2),[9],[42],1473⟩,⟨307,(3),[9],[42],29⟩,⟨307,(4),[9],[42],3⟩,⟨307,(5),[9],[42],3⟩,⟨307,(6),[9],[42],511⟩,⟨307,(7),[9],[42],29⟩,⟨307,(8),[9],[42],3⟩,⟨307,(9),[9],[42],3⟩,⟨307,(10),[9],[42],512⟩,⟨307,(11),[9],[42],29⟩,⟨307,(12),[9],[42],3⟩,⟨307,(13),[9],[42],3⟩,⟨307,(14),[9],[42],513⟩,⟨307,(15),[9],[42],29⟩,⟨307,(16),[9],[42],3⟩,⟨307,(17),[9],[42],3⟩,⟨307,(18),[9],[42],514⟩,⟨307,(19),[9],[42],29⟩,⟨308,(8),[9],[42],1474⟩,⟨308,(9),[9],[42],1475⟩,⟨308,(10),[9],[42],1474⟩,⟨308,(11),[9],[42],1476⟩,⟨309,(0),[9],[42],1188⟩,⟨309,(1),[9],[42],1189⟩,⟨309,(2),[9],[42],1190⟩,⟨309,(3),[9],[42],1191⟩,⟨309,(4),[9],[42],1477⟩,⟨311,(0),[9],[42],1478⟩,⟨311,(1),[9],[42],1479⟩,⟨311,(2),[9],[42],1480⟩,⟨311,(3),[9],[42],1481⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2720
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2721
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2722
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2723
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2724
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2725
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2726
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2727
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2728
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2729
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2730
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2731
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2732
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2733
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2734
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2735
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2736
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2737
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2738
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2739
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2740
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2741
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2742
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2743
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2744
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2745
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2746
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2747
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2748
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2749
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2750
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2751
end Section14Records_9_2720_2752

#print axioms solution
