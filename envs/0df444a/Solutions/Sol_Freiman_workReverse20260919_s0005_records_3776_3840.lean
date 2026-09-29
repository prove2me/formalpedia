-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3776_3840
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:31:21.817902+00:00
-- url     : https://prove2.me/submissions/cbc066a6-b75b-42cf-855d-8342dbc2cab1

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3776_3808
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3776_3808
private theorem valid3776 : RecordDataValid section14Catalog 5 (⟨228,(18),[1,2,5,6,13,14],[170],805⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3777 : RecordDataValid section14Catalog 5 (⟨228,(18),[5,6],[174],805⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3778 : RecordDataValid section14Catalog 5 (⟨228,(19),[1,2,5,6,13,14],[170],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3779 : RecordDataValid section14Catalog 5 (⟨228,(19),[5,6],[174],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3780 : RecordDataValid section14Catalog 5 (⟨228,(20),[1,2,5,6,13,14],[170],806⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3781 : RecordDataValid section14Catalog 5 (⟨228,(20),[5,6],[174],806⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3782 : RecordDataValid section14Catalog 5 (⟨228,(21),[1,2,5,6,13,14],[170],807⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3783 : RecordDataValid section14Catalog 5 (⟨228,(21),[5,6],[174],807⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3784 : RecordDataValid section14Catalog 5 (⟨228,(22),[1,2,5,6,13,14],[170],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3785 : RecordDataValid section14Catalog 5 (⟨228,(22),[5,6],[174],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3786 : RecordDataValid section14Catalog 5 (⟨228,(23),[1,2,5,6,13,14],[170],809⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3787 : RecordDataValid section14Catalog 5 (⟨228,(23),[5,6],[174],809⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3788 : RecordDataValid section14Catalog 5 (⟨228,(24),[1,2,5,6,13,14],[170],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3789 : RecordDataValid section14Catalog 5 (⟨228,(24),[5,6],[174],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3790 : RecordDataValid section14Catalog 5 (⟨230,(0),[1,2,5,6,13,14],[170],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3791 : RecordDataValid section14Catalog 5 (⟨230,(0),[5,6],[174],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3792 : RecordDataValid section14Catalog 5 (⟨230,(1),[1,2,5,6,13,14],[170],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3793 : RecordDataValid section14Catalog 5 (⟨230,(1),[5,6],[174],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3794 : RecordDataValid section14Catalog 5 (⟨230,(2),[1,2,5,6,13,14],[170],812⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3795 : RecordDataValid section14Catalog 5 (⟨230,(2),[5,6],[174],812⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3796 : RecordDataValid section14Catalog 5 (⟨230,(3),[1,2,5,6,13,14],[170],813⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3797 : RecordDataValid section14Catalog 5 (⟨230,(3),[5,6],[174],813⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3798 : RecordDataValid section14Catalog 5 (⟨230,(4),[1,2,5,6,13,14],[170],814⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨814,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],815⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3799 : RecordDataValid section14Catalog 5 (⟨230,(4),[5,6],[174],814⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨814,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],815⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3800 : RecordDataValid section14Catalog 5 (⟨230,(5),[1,2,5,6,13,14],[170],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3801 : RecordDataValid section14Catalog 5 (⟨230,(5),[5,6],[174],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3802 : RecordDataValid section14Catalog 5 (⟨230,(6),[1,2,5,6,13,14],[170],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3803 : RecordDataValid section14Catalog 5 (⟨230,(6),[5,6],[174],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3804 : RecordDataValid section14Catalog 5 (⟨230,(7),[1,5,6,13],[170],815⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨815,[1,4,5,6,8,9,10,12,13,16],816⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3805 : RecordDataValid section14Catalog 5 (⟨230,(7),[5,6],[174],1063⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1063,[3,5,6,7],1067⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3806 : RecordDataValid section14Catalog 5 (⟨230,(8),[1,2,5,6,13,14],[170],816⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3807 : RecordDataValid section14Catalog 5 (⟨230,(8),[5,6],[174],816⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3776_3808 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3776).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3776).take 32 = [⟨228,(18),[1,2,5,6,13,14],[170],805⟩,⟨228,(18),[5,6],[174],805⟩,⟨228,(19),[1,2,5,6,13,14],[170],804⟩,⟨228,(19),[5,6],[174],804⟩,⟨228,(20),[1,2,5,6,13,14],[170],806⟩,⟨228,(20),[5,6],[174],806⟩,⟨228,(21),[1,2,5,6,13,14],[170],807⟩,⟨228,(21),[5,6],[174],807⟩,⟨228,(22),[1,2,5,6,13,14],[170],808⟩,⟨228,(22),[5,6],[174],808⟩,⟨228,(23),[1,2,5,6,13,14],[170],809⟩,⟨228,(23),[5,6],[174],809⟩,⟨228,(24),[1,2,5,6,13,14],[170],808⟩,⟨228,(24),[5,6],[174],808⟩,⟨230,(0),[1,2,5,6,13,14],[170],810⟩,⟨230,(0),[5,6],[174],810⟩,⟨230,(1),[1,2,5,6,13,14],[170],811⟩,⟨230,(1),[5,6],[174],811⟩,⟨230,(2),[1,2,5,6,13,14],[170],812⟩,⟨230,(2),[5,6],[174],812⟩,⟨230,(3),[1,2,5,6,13,14],[170],813⟩,⟨230,(3),[5,6],[174],813⟩,⟨230,(4),[1,2,5,6,13,14],[170],814⟩,⟨230,(4),[5,6],[174],814⟩,⟨230,(5),[1,2,5,6,13,14],[170],810⟩,⟨230,(5),[5,6],[174],810⟩,⟨230,(6),[1,2,5,6,13,14],[170],811⟩,⟨230,(6),[5,6],[174],811⟩,⟨230,(7),[1,5,6,13],[170],815⟩,⟨230,(7),[5,6],[174],1063⟩,⟨230,(8),[1,2,5,6,13,14],[170],816⟩,⟨230,(8),[5,6],[174],816⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3776
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3777
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3778
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3779
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3780
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3781
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3782
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3783
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3784
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3785
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3786
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3787
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3788
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3789
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3790
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3791
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3792
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3793
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3794
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3795
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3796
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3797
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3798
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3799
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3800
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3801
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3802
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3803
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3804
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3805
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3806
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3807
end Section14Records_5_3776_3808

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3776_3808


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3808_3840
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3808_3840
private theorem valid3808 : RecordDataValid section14Catalog 5 (⟨230,(9),[5],[170],1375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1375,[4,5,8,9,12,16],1379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3809 : RecordDataValid section14Catalog 5 (⟨230,(9),[5,6],[174],1065⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1065,[3,5,6,7],1069⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3810 : RecordDataValid section14Catalog 5 (⟨230,(10),[1,2,5,6,13,14],[170],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3811 : RecordDataValid section14Catalog 5 (⟨230,(10),[5,6],[174],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3812 : RecordDataValid section14Catalog 5 (⟨230,(11),[1,2,5,6,13,14],[170],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3813 : RecordDataValid section14Catalog 5 (⟨230,(11),[5,6],[174],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3814 : RecordDataValid section14Catalog 5 (⟨230,(12),[1,5,13],[170],820⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨820,[1,4,5,8,9,10,12,13,16],821⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3815 : RecordDataValid section14Catalog 5 (⟨230,(12),[5,6],[174],1066⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1066,[3,5,6,7],1070⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3816 : RecordDataValid section14Catalog 5 (⟨230,(13),[1,2,5,6,13,14],[170],821⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨821,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],822⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3817 : RecordDataValid section14Catalog 5 (⟨230,(13),[5,6],[174],1066⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1066,[3,5,6,7],1070⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3818 : RecordDataValid section14Catalog 5 (⟨230,(14),[5],[170],1375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1375,[4,5,8,9,12,16],1379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3819 : RecordDataValid section14Catalog 5 (⟨230,(14),[5,6],[174],1065⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1065,[3,5,6,7],1069⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3820 : RecordDataValid section14Catalog 5 (⟨230,(15),[1,2,5,6,13,14],[170],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3821 : RecordDataValid section14Catalog 5 (⟨230,(15),[5,6],[174],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3822 : RecordDataValid section14Catalog 5 (⟨230,(16),[1,2,5,6,13,14],[170],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3823 : RecordDataValid section14Catalog 5 (⟨230,(16),[5,6],[174],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3824 : RecordDataValid section14Catalog 5 (⟨230,(17),[1,2,5,6,13,14],[170],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3825 : RecordDataValid section14Catalog 5 (⟨230,(17),[5,6],[174],1067⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1067,[3,5,6,7],1071⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3826 : RecordDataValid section14Catalog 5 (⟨230,(18),[1,2,5,6,13,14],[170],825⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨825,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],826⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3827 : RecordDataValid section14Catalog 5 (⟨230,(18),[5,6],[174],1067⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1067,[3,5,6,7],1071⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3828 : RecordDataValid section14Catalog 5 (⟨230,(19),[1,2,5,6,13,14],[170],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3829 : RecordDataValid section14Catalog 5 (⟨230,(19),[5,6],[174],1067⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1067,[3,5,6,7],1071⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3830 : RecordDataValid section14Catalog 5 (⟨230,(20),[1,2,5,6,13,14],[170],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3831 : RecordDataValid section14Catalog 5 (⟨230,(20),[5,6],[174],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3832 : RecordDataValid section14Catalog 5 (⟨230,(21),[1,2,5,6,13,14],[170],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3833 : RecordDataValid section14Catalog 5 (⟨230,(21),[5,6],[174],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3834 : RecordDataValid section14Catalog 5 (⟨230,(22),[1,2,5,6,13,14],[170],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3835 : RecordDataValid section14Catalog 5 (⟨230,(22),[5,6],[174],1068⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1068,[3,5,6,7],1072⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3836 : RecordDataValid section14Catalog 5 (⟨230,(23),[1,2,5,6,13,14],[170],829⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3837 : RecordDataValid section14Catalog 5 (⟨230,(23),[5,6],[174],1068⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1068,[3,5,6,7],1072⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3838 : RecordDataValid section14Catalog 5 (⟨230,(24),[1,2,5,6,13,14],[170],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3839 : RecordDataValid section14Catalog 5 (⟨230,(24),[5,6],[174],1068⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1068,[3,5,6,7],1072⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3808_3840 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3808).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3808).take 32 = [⟨230,(9),[5],[170],1375⟩,⟨230,(9),[5,6],[174],1065⟩,⟨230,(10),[1,2,5,6,13,14],[170],818⟩,⟨230,(10),[5,6],[174],818⟩,⟨230,(11),[1,2,5,6,13,14],[170],819⟩,⟨230,(11),[5,6],[174],819⟩,⟨230,(12),[1,5,13],[170],820⟩,⟨230,(12),[5,6],[174],1066⟩,⟨230,(13),[1,2,5,6,13,14],[170],821⟩,⟨230,(13),[5,6],[174],1066⟩,⟨230,(14),[5],[170],1375⟩,⟨230,(14),[5,6],[174],1065⟩,⟨230,(15),[1,2,5,6,13,14],[170],822⟩,⟨230,(15),[5,6],[174],822⟩,⟨230,(16),[1,2,5,6,13,14],[170],823⟩,⟨230,(16),[5,6],[174],823⟩,⟨230,(17),[1,2,5,6,13,14],[170],824⟩,⟨230,(17),[5,6],[174],1067⟩,⟨230,(18),[1,2,5,6,13,14],[170],825⟩,⟨230,(18),[5,6],[174],1067⟩,⟨230,(19),[1,2,5,6,13,14],[170],824⟩,⟨230,(19),[5,6],[174],1067⟩,⟨230,(20),[1,2,5,6,13,14],[170],826⟩,⟨230,(20),[5,6],[174],826⟩,⟨230,(21),[1,2,5,6,13,14],[170],827⟩,⟨230,(21),[5,6],[174],827⟩,⟨230,(22),[1,2,5,6,13,14],[170],828⟩,⟨230,(22),[5,6],[174],1068⟩,⟨230,(23),[1,2,5,6,13,14],[170],829⟩,⟨230,(23),[5,6],[174],1068⟩,⟨230,(24),[1,2,5,6,13,14],[170],828⟩,⟨230,(24),[5,6],[174],1068⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3808
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3809
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3810
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3811
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3812
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3813
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3814
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3815
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3816
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3817
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3818
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3819
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3820
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3821
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3822
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3823
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3824
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3825
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3826
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3827
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3828
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3829
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3830
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3831
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3832
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3833
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3834
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3835
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3836
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3837
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3838
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3839
end Section14Records_5_3808_3840

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3808_3840

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3776).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 3776 3808 3840 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_3776_3808 hnum) (Freiman.workReverse20260919_s0005_records_3808_3840 hnum))

#print axioms solution
