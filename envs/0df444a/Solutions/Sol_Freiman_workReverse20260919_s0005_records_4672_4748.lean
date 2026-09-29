-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4672_4748
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:42:16.758491+00:00
-- url     : https://prove2.me/submissions/09be1c54-5240-4052-a3a5-b3721e0e4f69

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4672_4704
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4672_4704
private theorem valid4672 : RecordDataValid section14Catalog 5 (⟨317,(13),[5],[170],1493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1493,[5,8,9,12],1498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4673 : RecordDataValid section14Catalog 5 (⟨317,(14),[5],[170],1494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1494,[5,8,9,12],1499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4674 : RecordDataValid section14Catalog 5 (⟨317,(15),[5],[170],1495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1495,[5,8,9,12],1500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4675 : RecordDataValid section14Catalog 5 (⟨318,(0),[5],[170],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4676 : RecordDataValid section14Catalog 5 (⟨318,(1),[5],[170],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4677 : RecordDataValid section14Catalog 5 (⟨318,(2),[5],[170],1498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1498,[5,8,9,12],1503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4678 : RecordDataValid section14Catalog 5 (⟨318,(3),[5],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4679 : RecordDataValid section14Catalog 5 (⟨318,(4),[5],[170],1498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1498,[5,8,9,12],1503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4680 : RecordDataValid section14Catalog 5 (⟨318,(5),[5],[170],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4681 : RecordDataValid section14Catalog 5 (⟨318,(6),[5],[170],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4682 : RecordDataValid section14Catalog 5 (⟨318,(7),[5],[170],1499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1499,[5,8,9,12],1504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4683 : RecordDataValid section14Catalog 5 (⟨318,(8),[5],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4684 : RecordDataValid section14Catalog 5 (⟨318,(9),[5],[170],1499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1499,[5,8,9,12],1504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4685 : RecordDataValid section14Catalog 5 (⟨318,(10),[5],[170],1500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1500,[5,8,9,12],1505⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4686 : RecordDataValid section14Catalog 5 (⟨318,(11),[5],[170],1501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1501,[5,8,9,12],1506⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4687 : RecordDataValid section14Catalog 5 (⟨318,(12),[5],[170],1502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1502,[5,8,9,12],1507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4688 : RecordDataValid section14Catalog 5 (⟨318,(13),[5],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4689 : RecordDataValid section14Catalog 5 (⟨318,(14),[5],[170],1502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1502,[5,8,9,12],1507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4690 : RecordDataValid section14Catalog 5 (⟨318,(15),[5],[170],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4691 : RecordDataValid section14Catalog 5 (⟨318,(16),[5],[170],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4692 : RecordDataValid section14Catalog 5 (⟨318,(17),[5],[170],1503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1503,[5,8,9,12],1508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4693 : RecordDataValid section14Catalog 5 (⟨318,(18),[5],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4694 : RecordDataValid section14Catalog 5 (⟨318,(19),[5],[170],1503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1503,[5,8,9,12],1508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4695 : RecordDataValid section14Catalog 5 (⟨319,(0),[5],[170],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4696 : RecordDataValid section14Catalog 5 (⟨319,(1),[5],[170],1229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1229,[3,5,7,8,9,11,12,15],1233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4697 : RecordDataValid section14Catalog 5 (⟨319,(2),[5],[170],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4698 : RecordDataValid section14Catalog 5 (⟨319,(3),[5],[170],1230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1230,[3,5,7,8,9,11,12,15],1234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4699 : RecordDataValid section14Catalog 5 (⟨319,(4),[5],[170],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4700 : RecordDataValid section14Catalog 5 (⟨319,(5),[5],[170],1232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1232,[3,5,7,8,9,11,12,15],1236⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4701 : RecordDataValid section14Catalog 5 (⟨319,(6),[5],[170],1504⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1504,[5,8,9,12],1509⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4702 : RecordDataValid section14Catalog 5 (⟨319,(7),[5],[170],1505⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1505,[5,8,9,12],1510⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4703 : RecordDataValid section14Catalog 5 (⟨319,(8),[5],[170],1235⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1235,[3,5,7,8,9,11,12,15],1239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4672_4704 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4672).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4672).take 32 = [⟨317,(13),[5],[170],1493⟩,⟨317,(14),[5],[170],1494⟩,⟨317,(15),[5],[170],1495⟩,⟨318,(0),[5],[170],882⟩,⟨318,(1),[5],[170],1497⟩,⟨318,(2),[5],[170],1498⟩,⟨318,(3),[5],[170],101⟩,⟨318,(4),[5],[170],1498⟩,⟨318,(5),[5],[170],882⟩,⟨318,(6),[5],[170],1497⟩,⟨318,(7),[5],[170],1499⟩,⟨318,(8),[5],[170],101⟩,⟨318,(9),[5],[170],1499⟩,⟨318,(10),[5],[170],1500⟩,⟨318,(11),[5],[170],1501⟩,⟨318,(12),[5],[170],1502⟩,⟨318,(13),[5],[170],101⟩,⟨318,(14),[5],[170],1502⟩,⟨318,(15),[5],[170],882⟩,⟨318,(16),[5],[170],1497⟩,⟨318,(17),[5],[170],1503⟩,⟨318,(18),[5],[170],101⟩,⟨318,(19),[5],[170],1503⟩,⟨319,(0),[5],[170],1231⟩,⟨319,(1),[5],[170],1229⟩,⟨319,(2),[5],[170],1228⟩,⟨319,(3),[5],[170],1230⟩,⟨319,(4),[5],[170],1231⟩,⟨319,(5),[5],[170],1232⟩,⟨319,(6),[5],[170],1504⟩,⟨319,(7),[5],[170],1505⟩,⟨319,(8),[5],[170],1235⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4672
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4673
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4674
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4675
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4676
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4677
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4678
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4679
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4680
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4681
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4682
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4683
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4684
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4685
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4686
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4687
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4688
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4689
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4690
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4691
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4692
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4693
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4694
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4695
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4696
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4697
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4698
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4699
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4700
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4701
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4702
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4703
end Section14Records_5_4672_4704

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4672_4704


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4704_4736
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4704_4736
private theorem valid4704 : RecordDataValid section14Catalog 5 (⟨319,(9),[5],[170],1236⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1236,[3,5,7,8,9,11,12,15],1240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4705 : RecordDataValid section14Catalog 5 (⟨319,(10),[5],[170],1506⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1506,[5,8,9,12],1511⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4706 : RecordDataValid section14Catalog 5 (⟨319,(11),[5],[170],1507⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1507,[5,8,9,12],1512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4707 : RecordDataValid section14Catalog 5 (⟨319,(12),[5],[170],1239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1239,[3,5,7,8,9,11,12,15],1243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4708 : RecordDataValid section14Catalog 5 (⟨319,(13),[5],[170],1240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1240,[3,5,7,8,9,11,12,15],1244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4709 : RecordDataValid section14Catalog 5 (⟨319,(14),[5],[170],1508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1508,[5,8,9,12],1513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4710 : RecordDataValid section14Catalog 5 (⟨319,(15),[5],[170],1508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1508,[5,8,9,12],1513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4711 : RecordDataValid section14Catalog 5 (⟨319,(16),[5],[170],1242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1242,[3,5,7,8,9,11,12,15],1246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4712 : RecordDataValid section14Catalog 5 (⟨319,(17),[5],[170],1243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1243,[3,5,7,8,9,11,12,15],1247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4713 : RecordDataValid section14Catalog 5 (⟨319,(18),[5],[170],1509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1509,[5,8,9,12],1514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4714 : RecordDataValid section14Catalog 5 (⟨319,(19),[5],[170],1509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1509,[5,8,9,12],1514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4715 : RecordDataValid section14Catalog 5 (⟨321,(0),[5],[170],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4716 : RecordDataValid section14Catalog 5 (⟨321,(1),[5],[170],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4717 : RecordDataValid section14Catalog 5 (⟨321,(2),[5],[170],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4718 : RecordDataValid section14Catalog 5 (⟨321,(3),[5],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4719 : RecordDataValid section14Catalog 5 (⟨321,(4),[5],[170],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4720 : RecordDataValid section14Catalog 5 (⟨321,(5),[5],[170],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4721 : RecordDataValid section14Catalog 5 (⟨321,(6),[5],[170],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4722 : RecordDataValid section14Catalog 5 (⟨321,(7),[5],[170],1510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1510,[5,8,9,12],1515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4723 : RecordDataValid section14Catalog 5 (⟨321,(8),[5],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4724 : RecordDataValid section14Catalog 5 (⟨321,(9),[5],[170],1510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1510,[5,8,9,12],1515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4725 : RecordDataValid section14Catalog 5 (⟨321,(10),[5],[170],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4726 : RecordDataValid section14Catalog 5 (⟨321,(11),[5],[170],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4727 : RecordDataValid section14Catalog 5 (⟨321,(12),[5],[170],1511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1511,[5,8,9,12],1516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4728 : RecordDataValid section14Catalog 5 (⟨321,(13),[5],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4729 : RecordDataValid section14Catalog 5 (⟨321,(14),[5],[170],1511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1511,[5,8,9,12],1516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4730 : RecordDataValid section14Catalog 5 (⟨321,(15),[5],[170],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4731 : RecordDataValid section14Catalog 5 (⟨321,(16),[5],[170],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4732 : RecordDataValid section14Catalog 5 (⟨321,(17),[5],[170],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4733 : RecordDataValid section14Catalog 5 (⟨321,(18),[5],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4734 : RecordDataValid section14Catalog 5 (⟨321,(19),[5],[170],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4735 : RecordDataValid section14Catalog 5 (⟨321,(20),[5],[170],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4704_4736 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4704).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4704).take 32 = [⟨319,(9),[5],[170],1236⟩,⟨319,(10),[5],[170],1506⟩,⟨319,(11),[5],[170],1507⟩,⟨319,(12),[5],[170],1239⟩,⟨319,(13),[5],[170],1240⟩,⟨319,(14),[5],[170],1508⟩,⟨319,(15),[5],[170],1508⟩,⟨319,(16),[5],[170],1242⟩,⟨319,(17),[5],[170],1243⟩,⟨319,(18),[5],[170],1509⟩,⟨319,(19),[5],[170],1509⟩,⟨321,(0),[5],[170],882⟩,⟨321,(1),[5],[170],1497⟩,⟨321,(2),[5],[170],1245⟩,⟨321,(3),[5],[170],101⟩,⟨321,(4),[5],[170],1245⟩,⟨321,(5),[5],[170],882⟩,⟨321,(6),[5],[170],1497⟩,⟨321,(7),[5],[170],1510⟩,⟨321,(8),[5],[170],101⟩,⟨321,(9),[5],[170],1510⟩,⟨321,(10),[5],[170],882⟩,⟨321,(11),[5],[170],1497⟩,⟨321,(12),[5],[170],1511⟩,⟨321,(13),[5],[170],101⟩,⟨321,(14),[5],[170],1511⟩,⟨321,(15),[5],[170],625⟩,⟨321,(16),[5],[170],626⟩,⟨321,(17),[5],[170],286⟩,⟨321,(18),[5],[170],101⟩,⟨321,(19),[5],[170],286⟩,⟨321,(20),[5],[170],882⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4704
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4705
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4706
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4707
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4708
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4709
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4710
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4711
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4712
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4713
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4714
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4715
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4716
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4717
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4718
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4719
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4720
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4721
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4722
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4723
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4724
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4725
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4726
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4727
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4728
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4729
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4730
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4731
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4732
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4733
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4734
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4735
end Section14Records_5_4704_4736

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4704_4736


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4736_4748
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4736_4748
private theorem valid4736 : RecordDataValid section14Catalog 5 (⟨321,(21),[5],[170],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4737 : RecordDataValid section14Catalog 5 (⟨321,(22),[5],[170],1512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1512,[5,8,9,12],1517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4738 : RecordDataValid section14Catalog 5 (⟨321,(23),[5],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4739 : RecordDataValid section14Catalog 5 (⟨321,(24),[5],[170],1512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1512,[5,8,9,12],1517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4740 : RecordDataValid section14Catalog 5 (⟨322,(5),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4741 : RecordDataValid section14Catalog 5 (⟨322,(7),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4742 : RecordDataValid section14Catalog 5 (⟨322,(8),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4743 : RecordDataValid section14Catalog 5 (⟨322,(9),[5],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4744 : RecordDataValid section14Catalog 5 (⟨322,(15),[5],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4745 : RecordDataValid section14Catalog 5 (⟨322,(16),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4746 : RecordDataValid section14Catalog 5 (⟨322,(17),[5],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4747 : RecordDataValid section14Catalog 5 (⟨322,(19),[5],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4736_4748 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4736).take 12, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4736).take 12 = [⟨321,(21),[5],[170],1497⟩,⟨321,(22),[5],[170],1512⟩,⟨321,(23),[5],[170],101⟩,⟨321,(24),[5],[170],1512⟩,⟨322,(5),[5],[170],3⟩,⟨322,(7),[5],[170],3⟩,⟨322,(8),[5],[170],3⟩,⟨322,(9),[5],[170],143⟩,⟨322,(15),[5],[170],48⟩,⟨322,(16),[5],[170],3⟩,⟨322,(17),[5],[170],48⟩,⟨322,(19),[5],[170],143⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4736
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4737
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4738
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4739
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4740
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4741
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4742
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4743
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4744
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4745
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4746
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4747
end Section14Records_5_4736_4748

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4736_4748

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4672).take 76, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 4672 4704 4748 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_4672_4704 hnum) (all_of_interval_split P xs 4704 4736 4748 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_4704_4736 hnum) (Freiman.workReverse20260919_s0005_records_4736_4748 hnum)))

#print axioms solution
