-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4608_4672
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:42:11.748918+00:00
-- url     : https://prove2.me/submissions/473aa206-cceb-42bb-ab71-0ea65ce4eef7

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4608_4640
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4608_4640
private theorem valid4608 : RecordDataValid section14Catalog 5 (⟨307,(6),[5],[170],511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨511,[1,2,5,6,9,10,13,14],512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4609 : RecordDataValid section14Catalog 5 (⟨307,(7),[5],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4610 : RecordDataValid section14Catalog 5 (⟨307,(8),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4611 : RecordDataValid section14Catalog 5 (⟨307,(9),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4612 : RecordDataValid section14Catalog 5 (⟨307,(10),[5],[170],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4613 : RecordDataValid section14Catalog 5 (⟨307,(11),[5],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4614 : RecordDataValid section14Catalog 5 (⟨307,(12),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4615 : RecordDataValid section14Catalog 5 (⟨307,(13),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4616 : RecordDataValid section14Catalog 5 (⟨307,(14),[5],[170],513⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨513,[1,2,5,6,9,10,13,14],514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4617 : RecordDataValid section14Catalog 5 (⟨307,(15),[5],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4618 : RecordDataValid section14Catalog 5 (⟨307,(16),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4619 : RecordDataValid section14Catalog 5 (⟨307,(17),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4620 : RecordDataValid section14Catalog 5 (⟨307,(18),[5],[170],514⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨514,[1,2,4,5,6,8,9,10,12,13,14,16],515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4621 : RecordDataValid section14Catalog 5 (⟨307,(19),[5],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4622 : RecordDataValid section14Catalog 5 (⟨308,(8),[5],[170],1474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1474,[5,8,9,12],1479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4623 : RecordDataValid section14Catalog 5 (⟨308,(9),[5],[170],1475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1475,[5,8,9,12],1480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4624 : RecordDataValid section14Catalog 5 (⟨308,(10),[5],[170],1474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1474,[5,8,9,12],1479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4625 : RecordDataValid section14Catalog 5 (⟨308,(11),[5],[170],1476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1476,[5,8,9,12],1481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4626 : RecordDataValid section14Catalog 5 (⟨309,(0),[5],[170],1188⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1188,[3,5,7,8,9,11,12,15],1192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4627 : RecordDataValid section14Catalog 5 (⟨309,(1),[5],[170],1189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1189,[3,5,7,8,9,11,12,15],1193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4628 : RecordDataValid section14Catalog 5 (⟨309,(2),[5],[170],1190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1190,[3,5,7,8,9,11,12,15],1194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4629 : RecordDataValid section14Catalog 5 (⟨309,(3),[5],[170],1191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1191,[3,5,7,8,9,11,12,15],1195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4630 : RecordDataValid section14Catalog 5 (⟨309,(4),[5],[170],1477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1477,[5,9],1482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4631 : RecordDataValid section14Catalog 5 (⟨311,(0),[5],[170],1478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1478,[5,8,9,12],1483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4632 : RecordDataValid section14Catalog 5 (⟨311,(1),[5],[170],1479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1479,[5,8,9,12],1484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4633 : RecordDataValid section14Catalog 5 (⟨311,(2),[5],[170],1480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1480,[5,8,9,12],1485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4634 : RecordDataValid section14Catalog 5 (⟨311,(3),[5],[170],1481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1481,[5,8,9,12],1486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4635 : RecordDataValid section14Catalog 5 (⟨312,(0),[5],[170],1482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1482,[5,8,9,12],1487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4636 : RecordDataValid section14Catalog 5 (⟨312,(1),[5],[170],1483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1483,[5,8,9,12],1488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4637 : RecordDataValid section14Catalog 5 (⟨312,(2),[5],[170],1482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1482,[5,8,9,12],1487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4638 : RecordDataValid section14Catalog 5 (⟨312,(3),[5],[170],1484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1484,[5,8,9,12],1489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4639 : RecordDataValid section14Catalog 5 (⟨313,(0),[5],[170],1200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1200,[3,5,7,8,9,11,12,15],1204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4608_4640 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4608).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4608).take 32 = [⟨307,(6),[5],[170],511⟩,⟨307,(7),[5],[170],29⟩,⟨307,(8),[5],[170],3⟩,⟨307,(9),[5],[170],3⟩,⟨307,(10),[5],[170],512⟩,⟨307,(11),[5],[170],29⟩,⟨307,(12),[5],[170],3⟩,⟨307,(13),[5],[170],3⟩,⟨307,(14),[5],[170],513⟩,⟨307,(15),[5],[170],29⟩,⟨307,(16),[5],[170],3⟩,⟨307,(17),[5],[170],3⟩,⟨307,(18),[5],[170],514⟩,⟨307,(19),[5],[170],29⟩,⟨308,(8),[5],[170],1474⟩,⟨308,(9),[5],[170],1475⟩,⟨308,(10),[5],[170],1474⟩,⟨308,(11),[5],[170],1476⟩,⟨309,(0),[5],[170],1188⟩,⟨309,(1),[5],[170],1189⟩,⟨309,(2),[5],[170],1190⟩,⟨309,(3),[5],[170],1191⟩,⟨309,(4),[5],[170],1477⟩,⟨311,(0),[5],[170],1478⟩,⟨311,(1),[5],[170],1479⟩,⟨311,(2),[5],[170],1480⟩,⟨311,(3),[5],[170],1481⟩,⟨312,(0),[5],[170],1482⟩,⟨312,(1),[5],[170],1483⟩,⟨312,(2),[5],[170],1482⟩,⟨312,(3),[5],[170],1484⟩,⟨313,(0),[5],[170],1200⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4608
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4609
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4610
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4611
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4612
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4613
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4614
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4615
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4616
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4617
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4618
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4619
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4620
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4621
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4622
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4623
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4624
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4625
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4626
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4627
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4628
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4629
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4630
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4631
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4632
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4633
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4634
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4635
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4636
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4637
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4638
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4639
end Section14Records_5_4608_4640

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4608_4640


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4640_4672
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4640_4672
private theorem valid4640 : RecordDataValid section14Catalog 5 (⟨313,(1),[5],[170],1201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1201,[3,5,7,8,9,11,12,15],1205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4641 : RecordDataValid section14Catalog 5 (⟨313,(2),[5],[170],1202⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1202,[3,5,7,8,9,11,12,15],1206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4642 : RecordDataValid section14Catalog 5 (⟨313,(3),[5],[170],1203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1203,[3,5,7,8,9,11,15],1207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4643 : RecordDataValid section14Catalog 5 (⟨315,(0),[5],[170],1485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1485,[5,8,9,12],1490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4644 : RecordDataValid section14Catalog 5 (⟨315,(1),[5],[170],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4645 : RecordDataValid section14Catalog 5 (⟨315,(2),[5],[170],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4646 : RecordDataValid section14Catalog 5 (⟨315,(3),[5],[170],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4647 : RecordDataValid section14Catalog 5 (⟨315,(4),[5],[170],1489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1489,[5,8,9,12],1494⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4648 : RecordDataValid section14Catalog 5 (⟨315,(5),[5],[170],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4649 : RecordDataValid section14Catalog 5 (⟨315,(6),[5],[170],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4650 : RecordDataValid section14Catalog 5 (⟨315,(7),[5],[170],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4651 : RecordDataValid section14Catalog 5 (⟨315,(8),[5],[170],1485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1485,[5,8,9,12],1490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4652 : RecordDataValid section14Catalog 5 (⟨315,(9),[5],[170],1490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1490,[5,8,9,12],1495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4653 : RecordDataValid section14Catalog 5 (⟨315,(10),[5],[170],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4654 : RecordDataValid section14Catalog 5 (⟨315,(11),[5],[170],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4655 : RecordDataValid section14Catalog 5 (⟨315,(12),[5],[170],1491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1491,[5,8,9,12],1496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4656 : RecordDataValid section14Catalog 5 (⟨315,(13),[5],[170],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4657 : RecordDataValid section14Catalog 5 (⟨315,(14),[5],[170],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4658 : RecordDataValid section14Catalog 5 (⟨315,(15),[5],[170],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4659 : RecordDataValid section14Catalog 5 (⟨317,(0),[5],[170],1211⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1211,[3,5,7,8,9,11,12,15],1215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4660 : RecordDataValid section14Catalog 5 (⟨317,(1),[5],[170],1212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1212,[3,5,7,8,9,11,12,15],1216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4661 : RecordDataValid section14Catalog 5 (⟨317,(2),[5],[170],1213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1213,[3,5,7,8,9,11,12,15],1217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4662 : RecordDataValid section14Catalog 5 (⟨317,(3),[5],[170],1214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1214,[3,5,7,8,9,11,12,15],1218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4663 : RecordDataValid section14Catalog 5 (⟨317,(4),[5],[170],1215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1215,[3,5,7,8,9,11,12,15],1219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4664 : RecordDataValid section14Catalog 5 (⟨317,(5),[5],[170],1216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1216,[3,5,7,8,9,11,12,15],1220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4665 : RecordDataValid section14Catalog 5 (⟨317,(6),[5],[170],1217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1217,[3,5,7,8,9,11,12,15],1221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4666 : RecordDataValid section14Catalog 5 (⟨317,(7),[5],[170],1218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1218,[3,5,7,8,9,11,12,15],1222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4667 : RecordDataValid section14Catalog 5 (⟨317,(8),[5],[170],1492⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1492,[5,8,9,12],1497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4668 : RecordDataValid section14Catalog 5 (⟨317,(9),[5],[170],1493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1493,[5,8,9,12],1498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4669 : RecordDataValid section14Catalog 5 (⟨317,(10),[5],[170],1494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1494,[5,8,9,12],1499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4670 : RecordDataValid section14Catalog 5 (⟨317,(11),[5],[170],1495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1495,[5,8,9,12],1500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4671 : RecordDataValid section14Catalog 5 (⟨317,(12),[5],[170],1496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1496,[5,8,9,12],1501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4640_4672 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4640).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4640).take 32 = [⟨313,(1),[5],[170],1201⟩,⟨313,(2),[5],[170],1202⟩,⟨313,(3),[5],[170],1203⟩,⟨315,(0),[5],[170],1485⟩,⟨315,(1),[5],[170],1486⟩,⟨315,(2),[5],[170],1487⟩,⟨315,(3),[5],[170],1488⟩,⟨315,(4),[5],[170],1489⟩,⟨315,(5),[5],[170],1486⟩,⟨315,(6),[5],[170],1487⟩,⟨315,(7),[5],[170],1488⟩,⟨315,(8),[5],[170],1485⟩,⟨315,(9),[5],[170],1490⟩,⟨315,(10),[5],[170],1487⟩,⟨315,(11),[5],[170],1488⟩,⟨315,(12),[5],[170],1491⟩,⟨315,(13),[5],[170],1486⟩,⟨315,(14),[5],[170],1487⟩,⟨315,(15),[5],[170],1488⟩,⟨317,(0),[5],[170],1211⟩,⟨317,(1),[5],[170],1212⟩,⟨317,(2),[5],[170],1213⟩,⟨317,(3),[5],[170],1214⟩,⟨317,(4),[5],[170],1215⟩,⟨317,(5),[5],[170],1216⟩,⟨317,(6),[5],[170],1217⟩,⟨317,(7),[5],[170],1218⟩,⟨317,(8),[5],[170],1492⟩,⟨317,(9),[5],[170],1493⟩,⟨317,(10),[5],[170],1494⟩,⟨317,(11),[5],[170],1495⟩,⟨317,(12),[5],[170],1496⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4640
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4641
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4642
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4643
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4644
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4645
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4646
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4647
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4648
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4649
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4650
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4651
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4652
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4653
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4654
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4655
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4656
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4657
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4658
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4659
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4660
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4661
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4662
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4663
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4664
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4665
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4666
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4667
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4668
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4669
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4670
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4671
end Section14Records_5_4640_4672

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4640_4672

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4608).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 4608 4640 4672 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_4608_4640 hnum) (Freiman.workReverse20260919_s0005_records_4640_4672 hnum))

#print axioms solution
