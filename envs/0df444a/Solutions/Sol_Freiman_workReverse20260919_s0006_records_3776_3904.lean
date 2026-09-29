-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3776_3904
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:43:18.509291+00:00
-- url     : https://prove2.me/submissions/30f7866f-f7b3-4f6e-902a-1464e5808ee8

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3776_3808
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3776_3808
private theorem valid3776 : RecordDataValid section14Catalog 6 (⟨242,(2),[5,6],[174],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3777 : RecordDataValid section14Catalog 6 (⟨242,(3),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3778 : RecordDataValid section14Catalog 6 (⟨242,(3),[5,6],[174],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3779 : RecordDataValid section14Catalog 6 (⟨242,(4),[1,2,5,6],[170],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3780 : RecordDataValid section14Catalog 6 (⟨242,(4),[5,6],[174],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3781 : RecordDataValid section14Catalog 6 (⟨242,(5),[1,2,5,6],[170],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3782 : RecordDataValid section14Catalog 6 (⟨242,(5),[5,6],[174],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3783 : RecordDataValid section14Catalog 6 (⟨242,(6),[1,2,5,6],[170],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3784 : RecordDataValid section14Catalog 6 (⟨242,(6),[5,6],[174],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3785 : RecordDataValid section14Catalog 6 (⟨242,(7),[1,2,5,6],[170],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3786 : RecordDataValid section14Catalog 6 (⟨242,(7),[5,6],[174],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3787 : RecordDataValid section14Catalog 6 (⟨242,(8),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3788 : RecordDataValid section14Catalog 6 (⟨242,(8),[5,6],[174],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3789 : RecordDataValid section14Catalog 6 (⟨242,(9),[1,2,5,6],[170],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3790 : RecordDataValid section14Catalog 6 (⟨242,(9),[5,6],[174],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3791 : RecordDataValid section14Catalog 6 (⟨242,(10),[1,2,5,6],[170],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3792 : RecordDataValid section14Catalog 6 (⟨242,(10),[5,6],[174],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3793 : RecordDataValid section14Catalog 6 (⟨242,(11),[1,2,5,6],[170],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3794 : RecordDataValid section14Catalog 6 (⟨242,(11),[5,6],[174],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3795 : RecordDataValid section14Catalog 6 (⟨242,(12),[1,2,5,6],[170],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3796 : RecordDataValid section14Catalog 6 (⟨242,(12),[5,6],[174],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3797 : RecordDataValid section14Catalog 6 (⟨242,(13),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3798 : RecordDataValid section14Catalog 6 (⟨242,(13),[5,6],[174],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3799 : RecordDataValid section14Catalog 6 (⟨242,(14),[1,2,5,6],[170],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3800 : RecordDataValid section14Catalog 6 (⟨242,(14),[5,6],[174],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3801 : RecordDataValid section14Catalog 6 (⟨242,(15),[1,2,5,6],[170],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3802 : RecordDataValid section14Catalog 6 (⟨242,(15),[5,6],[174],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3803 : RecordDataValid section14Catalog 6 (⟨242,(16),[1,2,5,6],[170],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3804 : RecordDataValid section14Catalog 6 (⟨242,(16),[5,6],[174],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3805 : RecordDataValid section14Catalog 6 (⟨242,(17),[1,2,5,6],[170],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3806 : RecordDataValid section14Catalog 6 (⟨242,(17),[5,6],[174],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3807 : RecordDataValid section14Catalog 6 (⟨242,(18),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3776_3808 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3776).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3776).take 32 = [⟨242,(2),[5,6],[174],873⟩,⟨242,(3),[1,2,5,6],[170],101⟩,⟨242,(3),[5,6],[174],101⟩,⟨242,(4),[1,2,5,6],[170],873⟩,⟨242,(4),[5,6],[174],873⟩,⟨242,(5),[1,2,5,6],[170],632⟩,⟨242,(5),[5,6],[174],632⟩,⟨242,(6),[1,2,5,6],[170],872⟩,⟨242,(6),[5,6],[174],872⟩,⟨242,(7),[1,2,5,6],[170],874⟩,⟨242,(7),[5,6],[174],874⟩,⟨242,(8),[1,2,5,6],[170],101⟩,⟨242,(8),[5,6],[174],101⟩,⟨242,(9),[1,2,5,6],[170],874⟩,⟨242,(9),[5,6],[174],874⟩,⟨242,(10),[1,2,5,6],[170],632⟩,⟨242,(10),[5,6],[174],632⟩,⟨242,(11),[1,2,5,6],[170],872⟩,⟨242,(11),[5,6],[174],872⟩,⟨242,(12),[1,2,5,6],[170],875⟩,⟨242,(12),[5,6],[174],875⟩,⟨242,(13),[1,2,5,6],[170],101⟩,⟨242,(13),[5,6],[174],101⟩,⟨242,(14),[1,2,5,6],[170],875⟩,⟨242,(14),[5,6],[174],875⟩,⟨242,(15),[1,2,5,6],[170],625⟩,⟨242,(15),[5,6],[174],625⟩,⟨242,(16),[1,2,5,6],[170],626⟩,⟨242,(16),[5,6],[174],626⟩,⟨242,(17),[1,2,5,6],[170],286⟩,⟨242,(17),[5,6],[174],286⟩,⟨242,(18),[1,2,5,6],[170],101⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3776
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3777
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3778
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3779
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3780
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3781
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3782
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3783
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3784
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3785
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3786
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3787
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3788
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3789
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3790
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3791
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3792
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3793
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3794
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3795
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3796
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3797
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3798
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3799
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3800
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3801
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3802
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3803
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3804
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3805
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3806
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3807
end Section14Records_6_3776_3808

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3776_3808


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3808_3840
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3808_3840
private theorem valid3808 : RecordDataValid section14Catalog 6 (⟨242,(18),[5,6],[174],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3809 : RecordDataValid section14Catalog 6 (⟨242,(19),[1,2,5,6],[170],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3810 : RecordDataValid section14Catalog 6 (⟨242,(19),[5,6],[174],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3811 : RecordDataValid section14Catalog 6 (⟨242,(20),[1,2,5,6],[170],876⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨876,[1,2,4,5,6,8,9,10,12],877⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3812 : RecordDataValid section14Catalog 6 (⟨242,(20),[5,6],[174],876⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨876,[1,2,4,5,6,8,9,10,12],877⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3813 : RecordDataValid section14Catalog 6 (⟨242,(21),[1,2,5,6],[170],877⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨877,[1,2,4,5,6,8,9,10,12],878⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3814 : RecordDataValid section14Catalog 6 (⟨242,(21),[5,6],[174],877⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨877,[1,2,4,5,6,8,9,10,12],878⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3815 : RecordDataValid section14Catalog 6 (⟨242,(22),[1,2,5,6],[170],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3816 : RecordDataValid section14Catalog 6 (⟨242,(22),[5,6],[174],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3817 : RecordDataValid section14Catalog 6 (⟨242,(23),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3818 : RecordDataValid section14Catalog 6 (⟨242,(23),[5,6],[174],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3819 : RecordDataValid section14Catalog 6 (⟨242,(24),[1,2,5,6],[170],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3820 : RecordDataValid section14Catalog 6 (⟨242,(24),[5,6],[174],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3821 : RecordDataValid section14Catalog 6 (⟨243,(5),[1,2,5,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3822 : RecordDataValid section14Catalog 6 (⟨243,(5),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3823 : RecordDataValid section14Catalog 6 (⟨243,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3824 : RecordDataValid section14Catalog 6 (⟨243,(7),[6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3825 : RecordDataValid section14Catalog 6 (⟨243,(8),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3826 : RecordDataValid section14Catalog 6 (⟨243,(8),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3827 : RecordDataValid section14Catalog 6 (⟨243,(9),[5,6],[174],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3828 : RecordDataValid section14Catalog 6 (⟨243,(9),[5,6,13,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3829 : RecordDataValid section14Catalog 6 (⟨243,(15),[1,2,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3830 : RecordDataValid section14Catalog 6 (⟨243,(15),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3831 : RecordDataValid section14Catalog 6 (⟨243,(16),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3832 : RecordDataValid section14Catalog 6 (⟨243,(16),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3833 : RecordDataValid section14Catalog 6 (⟨243,(17),[1,2,5,6,13,14],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3834 : RecordDataValid section14Catalog 6 (⟨243,(17),[5,6],[174],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3835 : RecordDataValid section14Catalog 6 (⟨243,(19),[2,5,6,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3836 : RecordDataValid section14Catalog 6 (⟨243,(19),[5,6],[174],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3837 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3838 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3839 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3808_3840 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3808).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3808).take 32 = [⟨242,(18),[5,6],[174],101⟩,⟨242,(19),[1,2,5,6],[170],286⟩,⟨242,(19),[5,6],[174],286⟩,⟨242,(20),[1,2,5,6],[170],876⟩,⟨242,(20),[5,6],[174],876⟩,⟨242,(21),[1,2,5,6],[170],877⟩,⟨242,(21),[5,6],[174],877⟩,⟨242,(22),[1,2,5,6],[170],287⟩,⟨242,(22),[5,6],[174],287⟩,⟨242,(23),[1,2,5,6],[170],101⟩,⟨242,(23),[5,6],[174],101⟩,⟨242,(24),[1,2,5,6],[170],287⟩,⟨242,(24),[5,6],[174],287⟩,⟨243,(5),[1,2,5,6,14],[170],3⟩,⟨243,(5),[5,6],[174],3⟩,⟨243,(7),[1,2,5,6,13,14],[170],3⟩,⟨243,(7),[6],[174],3⟩,⟨243,(8),[1,5,6,13,14],[170],3⟩,⟨243,(8),[5,6],[174],3⟩,⟨243,(9),[5,6],[174],143⟩,⟨243,(9),[5,6,13,14],[170],143⟩,⟨243,(15),[1,2,6,14],[170],3⟩,⟨243,(15),[5,6],[174],3⟩,⟨243,(16),[1,5,6,13,14],[170],3⟩,⟨243,(16),[5,6],[174],3⟩,⟨243,(17),[1,2,5,6,13,14],[170],48⟩,⟨243,(17),[5,6],[174],48⟩,⟨243,(19),[2,5,6,14],[170],143⟩,⟨243,(19),[5,6],[174],143⟩,⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩,⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3808
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3809
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3810
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3811
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3812
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3813
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3814
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3815
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3816
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3817
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3818
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3819
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3820
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3821
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3822
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3823
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3824
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3825
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3826
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3827
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3828
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3829
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3830
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3831
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3832
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3833
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3834
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3835
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3836
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3837
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3838
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3839
end Section14Records_6_3808_3840

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3808_3840


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3840_3872
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3840_3872
private theorem valid3840 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3841 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3842 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3843 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3844 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3845 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[146],885⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨885,[1,2,3,5,6,7,13,14,15],887⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3846 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3847 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[150],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3848 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[174],908⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨908,[1,2,3,5,6,7,13,14,15],910⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3849 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[186],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3850 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3851 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3852 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,2,5,6,14],[190],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3853 : RecordDataValid section14Catalog 6 (⟨245,(-1),[1,5,6,13],[194,198],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3854 : RecordDataValid section14Catalog 6 (⟨245,(-1),[2,4,6,8,10,14,16],[0,4],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3855 : RecordDataValid section14Catalog 6 (⟨245,(-1),[2,6,9,10,14],[16,20],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3856 : RecordDataValid section14Catalog 6 (⟨245,(-1),[2,6,14],[40,44,56,60],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3857 : RecordDataValid section14Catalog 6 (⟨245,(-1),[2,6,14],[211,215,235,239,251,255],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3858 : RecordDataValid section14Catalog 6 (⟨245,(-1),[5,6],[131,135],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3859 : RecordDataValid section14Catalog 6 (⟨245,(-1),[6],[195,199],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3860 : RecordDataValid section14Catalog 6 (⟨247,(0),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3861 : RecordDataValid section14Catalog 6 (⟨247,(1),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3862 : RecordDataValid section14Catalog 6 (⟨247,(2),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3863 : RecordDataValid section14Catalog 6 (⟨247,(3),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3864 : RecordDataValid section14Catalog 6 (⟨247,(4),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3865 : RecordDataValid section14Catalog 6 (⟨247,(5),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3866 : RecordDataValid section14Catalog 6 (⟨247,(6),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3867 : RecordDataValid section14Catalog 6 (⟨247,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3868 : RecordDataValid section14Catalog 6 (⟨247,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3869 : RecordDataValid section14Catalog 6 (⟨247,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3870 : RecordDataValid section14Catalog 6 (⟨247,(10),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3871 : RecordDataValid section14Catalog 6 (⟨247,(11),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3840_3872 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3840).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3840).take 32 = [⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩,⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩,⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩,⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩,⟨245,(-1),[1,2,5,6,13,14],[146],885⟩,⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩,⟨245,(-1),[1,2,5,6,13,14],[150],887⟩,⟨245,(-1),[1,2,5,6,13,14],[174],908⟩,⟨245,(-1),[1,2,5,6,13,14],[186],909⟩,⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩,⟨245,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨245,(-1),[1,2,5,6,14],[190],909⟩,⟨245,(-1),[1,5,6,13],[194,198],910⟩,⟨245,(-1),[2,4,6,8,10,14,16],[0,4],882⟩,⟨245,(-1),[2,6,9,10,14],[16,20],882⟩,⟨245,(-1),[2,6,14],[40,44,56,60],882⟩,⟨245,(-1),[2,6,14],[211,215,235,239,251,255],886⟩,⟨245,(-1),[5,6],[131,135],886⟩,⟨245,(-1),[6],[195,199],886⟩,⟨247,(0),[1,2,5,6,13,14],[170],3⟩,⟨247,(1),[1,2,5,6,13,14],[170],3⟩,⟨247,(2),[1,2,5,6,13,14],[170],3⟩,⟨247,(3),[1,2,5,6,13,14],[170],3⟩,⟨247,(4),[1,2,5,6,13,14],[170],3⟩,⟨247,(5),[1,2,5,6,13,14],[170],3⟩,⟨247,(6),[1,2,5,6,13,14],[170],3⟩,⟨247,(7),[1,2,5,6,13,14],[170],3⟩,⟨247,(8),[1,2,5,6,13,14],[170],3⟩,⟨247,(9),[1,2,5,6,13,14],[170],3⟩,⟨247,(10),[1,2,5,6,13,14],[170],3⟩,⟨247,(11),[1,2,5,6,13,14],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3840
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3841
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3842
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3843
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3844
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3845
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3846
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3847
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3848
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3849
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3850
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3851
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3852
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3853
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3854
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3855
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3856
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3857
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3858
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3859
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3860
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3861
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3862
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3863
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3864
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3865
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3866
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3867
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3868
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3869
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3870
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3871
end Section14Records_6_3840_3872

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3840_3872


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3872_3904
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3872_3904
private theorem valid3872 : RecordDataValid section14Catalog 6 (⟨247,(12),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3873 : RecordDataValid section14Catalog 6 (⟨247,(13),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3874 : RecordDataValid section14Catalog 6 (⟨247,(14),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3875 : RecordDataValid section14Catalog 6 (⟨247,(15),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3876 : RecordDataValid section14Catalog 6 (⟨247,(16),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3877 : RecordDataValid section14Catalog 6 (⟨247,(17),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3878 : RecordDataValid section14Catalog 6 (⟨247,(18),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3879 : RecordDataValid section14Catalog 6 (⟨247,(19),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3880 : RecordDataValid section14Catalog 6 (⟨247,(20),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3881 : RecordDataValid section14Catalog 6 (⟨247,(21),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3882 : RecordDataValid section14Catalog 6 (⟨247,(22),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3883 : RecordDataValid section14Catalog 6 (⟨247,(23),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3884 : RecordDataValid section14Catalog 6 (⟨247,(24),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3885 : RecordDataValid section14Catalog 6 (⟨249,(0),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3886 : RecordDataValid section14Catalog 6 (⟨249,(1),[2,5,6,14],[170],924⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨924,[2,3,5,6,7,14,15],928⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3887 : RecordDataValid section14Catalog 6 (⟨249,(2),[1,2,5,6,13,14],[170],888⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨888,[1,2,3,4,5,6,7,8,13,14,15,16],890⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3888 : RecordDataValid section14Catalog 6 (⟨249,(3),[1,2,5,6,13,14],[170],889⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨889,[1,2,3,4,5,6,7,8,13,14,15,16],891⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3889 : RecordDataValid section14Catalog 6 (⟨249,(4),[1,2,5,6,13,14],[170],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3890 : RecordDataValid section14Catalog 6 (⟨249,(5),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3891 : RecordDataValid section14Catalog 6 (⟨249,(6),[2,5,6,14],[170],924⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨924,[2,3,5,6,7,14,15],928⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3892 : RecordDataValid section14Catalog 6 (⟨249,(7),[1,2,5,6,13,14],[170],888⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨888,[1,2,3,4,5,6,7,8,13,14,15,16],890⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3893 : RecordDataValid section14Catalog 6 (⟨249,(8),[1,2,5,6,13,14],[170],889⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨889,[1,2,3,4,5,6,7,8,13,14,15,16],891⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3894 : RecordDataValid section14Catalog 6 (⟨249,(9),[1,2,5,6,13,14],[170],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3895 : RecordDataValid section14Catalog 6 (⟨249,(10),[1,2,5,6,13,14],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3896 : RecordDataValid section14Catalog 6 (⟨249,(11),[2,5,6,14],[170],891⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨891,[1,2,3,4,5,6,7,8,13,14,15,16],893⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3897 : RecordDataValid section14Catalog 6 (⟨249,(12),[1,2,5,6,13,14],[170],891⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨891,[1,2,3,4,5,6,7,8,13,14,15,16],893⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3898 : RecordDataValid section14Catalog 6 (⟨249,(13),[1,2,5,6,13,14],[170],891⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨891,[1,2,3,4,5,6,7,8,13,14,15,16],893⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3899 : RecordDataValid section14Catalog 6 (⟨249,(14),[1,2,5,6,13,14],[170],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3900 : RecordDataValid section14Catalog 6 (⟨249,(15),[1,2,5,6,13,14],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3901 : RecordDataValid section14Catalog 6 (⟨249,(16),[2,5,6,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3902 : RecordDataValid section14Catalog 6 (⟨249,(17),[1,2,5,6,13,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3903 : RecordDataValid section14Catalog 6 (⟨249,(18),[1,2,5,6,13,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3872_3904 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3872).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3872).take 32 = [⟨247,(12),[1,2,5,6,13,14],[170],3⟩,⟨247,(13),[1,2,5,6,13,14],[170],3⟩,⟨247,(14),[1,2,5,6,13,14],[170],3⟩,⟨247,(15),[1,2,5,6,13,14],[170],3⟩,⟨247,(16),[1,2,5,6,13,14],[170],3⟩,⟨247,(17),[1,2,5,6,13,14],[170],3⟩,⟨247,(18),[1,2,5,6,13,14],[170],3⟩,⟨247,(19),[1,2,5,6,13,14],[170],3⟩,⟨247,(20),[1,2,5,6,13,14],[170],3⟩,⟨247,(21),[1,2,5,6,13,14],[170],3⟩,⟨247,(22),[1,2,5,6,13,14],[170],3⟩,⟨247,(23),[1,2,5,6,13,14],[170],3⟩,⟨247,(24),[1,2,5,6,13,14],[170],3⟩,⟨249,(0),[1,2,5,6,13,14],[170],10⟩,⟨249,(1),[2,5,6,14],[170],924⟩,⟨249,(2),[1,2,5,6,13,14],[170],888⟩,⟨249,(3),[1,2,5,6,13,14],[170],889⟩,⟨249,(4),[1,2,5,6,13,14],[170],890⟩,⟨249,(5),[1,2,5,6,13,14],[170],10⟩,⟨249,(6),[2,5,6,14],[170],924⟩,⟨249,(7),[1,2,5,6,13,14],[170],888⟩,⟨249,(8),[1,2,5,6,13,14],[170],889⟩,⟨249,(9),[1,2,5,6,13,14],[170],890⟩,⟨249,(10),[1,2,5,6,13,14],[170],18⟩,⟨249,(11),[2,5,6,14],[170],891⟩,⟨249,(12),[1,2,5,6,13,14],[170],891⟩,⟨249,(13),[1,2,5,6,13,14],[170],891⟩,⟨249,(14),[1,2,5,6,13,14],[170],890⟩,⟨249,(15),[1,2,5,6,13,14],[170],21⟩,⟨249,(16),[2,5,6,14],[170],892⟩,⟨249,(17),[1,2,5,6,13,14],[170],892⟩,⟨249,(18),[1,2,5,6,13,14],[170],892⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3872
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3873
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3874
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3875
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3876
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3877
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3878
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3879
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3880
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3881
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3882
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3883
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3884
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3885
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3886
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3887
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3888
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3889
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3890
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3891
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3892
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3893
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3894
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3895
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3896
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3897
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3898
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3899
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3900
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3901
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3902
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3903
end Section14Records_6_3872_3904

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3872_3904

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3776).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 3776 3840 3904 (by decide) (by decide) (all_of_interval_split P xs 3776 3808 3840 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3776_3808 hnum) (Freiman.workReverse20260919_s0006_records_3808_3840 hnum)) (all_of_interval_split P xs 3840 3872 3904 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3840_3872 hnum) (Freiman.workReverse20260919_s0006_records_3872_3904 hnum)))

#print axioms solution
