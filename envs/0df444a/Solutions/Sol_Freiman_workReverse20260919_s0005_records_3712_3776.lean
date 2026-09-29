-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3712_3776
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:31:17.588965+00:00
-- url     : https://prove2.me/submissions/a84e353f-e41e-4cda-a7ea-387a4f2f4c17

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3712_3744
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3712_3744
private theorem valid3712 : RecordDataValid section14Catalog 5 (⟨227,(11),[1,2,5,6,13,14],[170],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3713 : RecordDataValid section14Catalog 5 (⟨227,(11),[5,6],[174],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3714 : RecordDataValid section14Catalog 5 (⟨227,(12),[1,2,5,6,13,14],[170],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3715 : RecordDataValid section14Catalog 5 (⟨227,(12),[5,6],[174],1058⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1058,[3,5,6,7],1062⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3716 : RecordDataValid section14Catalog 5 (⟨227,(13),[1,2,5,6,13,14],[170],780⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3717 : RecordDataValid section14Catalog 5 (⟨227,(13),[5,6],[174],1059⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1059,[3,5,6,7],1063⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3718 : RecordDataValid section14Catalog 5 (⟨227,(14),[1,2,5,6,13,14],[170],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3719 : RecordDataValid section14Catalog 5 (⟨227,(14),[5,6],[174],1058⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1058,[3,5,6,7],1062⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3720 : RecordDataValid section14Catalog 5 (⟨227,(15),[1,2,5,6,13,14],[170],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3721 : RecordDataValid section14Catalog 5 (⟨227,(15),[5,6],[174],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3722 : RecordDataValid section14Catalog 5 (⟨227,(16),[1,2,5,6,13,14],[170],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3723 : RecordDataValid section14Catalog 5 (⟨227,(16),[5,6],[174],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3724 : RecordDataValid section14Catalog 5 (⟨227,(17),[1,2,5,6,13,14],[170],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3725 : RecordDataValid section14Catalog 5 (⟨227,(17),[5,6],[174],1060⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1060,[3,5,6,7],1064⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3726 : RecordDataValid section14Catalog 5 (⟨227,(18),[1,2,5,6,13,14],[170],784⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3727 : RecordDataValid section14Catalog 5 (⟨227,(18),[5,6],[174],1060⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1060,[3,5,6,7],1064⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3728 : RecordDataValid section14Catalog 5 (⟨227,(19),[1,2,5,6,13,14],[170],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3729 : RecordDataValid section14Catalog 5 (⟨227,(19),[5,6],[174],1060⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1060,[3,5,6,7],1064⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3730 : RecordDataValid section14Catalog 5 (⟨227,(20),[1,2,5,6,13,14],[170],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3731 : RecordDataValid section14Catalog 5 (⟨227,(20),[5,6],[174],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3732 : RecordDataValid section14Catalog 5 (⟨227,(21),[1,2,5,6,13,14],[170],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3733 : RecordDataValid section14Catalog 5 (⟨227,(21),[5,6],[174],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3734 : RecordDataValid section14Catalog 5 (⟨227,(22),[1,2,5,6,13,14],[170],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3735 : RecordDataValid section14Catalog 5 (⟨227,(22),[5,6],[174],1061⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1061,[3,5,6,7],1065⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3736 : RecordDataValid section14Catalog 5 (⟨227,(23),[1,2,5,6,13,14],[170],788⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3737 : RecordDataValid section14Catalog 5 (⟨227,(23),[5,6],[174],1062⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1062,[3,5,6,7],1066⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3738 : RecordDataValid section14Catalog 5 (⟨227,(24),[1,2,5,6,13,14],[170],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3739 : RecordDataValid section14Catalog 5 (⟨227,(24),[5,6],[174],1061⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1061,[3,5,6,7],1065⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3740 : RecordDataValid section14Catalog 5 (⟨228,(0),[1,2,5,6,13,14],[170],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3741 : RecordDataValid section14Catalog 5 (⟨228,(0),[5,6],[174],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3742 : RecordDataValid section14Catalog 5 (⟨228,(1),[1,2,5,6,13,14],[170],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3743 : RecordDataValid section14Catalog 5 (⟨228,(1),[5,6],[174],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3712_3744 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3712).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3712).take 32 = [⟨227,(11),[1,2,5,6,13,14],[170],778⟩,⟨227,(11),[5,6],[174],778⟩,⟨227,(12),[1,2,5,6,13,14],[170],779⟩,⟨227,(12),[5,6],[174],1058⟩,⟨227,(13),[1,2,5,6,13,14],[170],780⟩,⟨227,(13),[5,6],[174],1059⟩,⟨227,(14),[1,2,5,6,13,14],[170],779⟩,⟨227,(14),[5,6],[174],1058⟩,⟨227,(15),[1,2,5,6,13,14],[170],781⟩,⟨227,(15),[5,6],[174],781⟩,⟨227,(16),[1,2,5,6,13,14],[170],782⟩,⟨227,(16),[5,6],[174],782⟩,⟨227,(17),[1,2,5,6,13,14],[170],783⟩,⟨227,(17),[5,6],[174],1060⟩,⟨227,(18),[1,2,5,6,13,14],[170],784⟩,⟨227,(18),[5,6],[174],1060⟩,⟨227,(19),[1,2,5,6,13,14],[170],783⟩,⟨227,(19),[5,6],[174],1060⟩,⟨227,(20),[1,2,5,6,13,14],[170],785⟩,⟨227,(20),[5,6],[174],785⟩,⟨227,(21),[1,2,5,6,13,14],[170],786⟩,⟨227,(21),[5,6],[174],786⟩,⟨227,(22),[1,2,5,6,13,14],[170],787⟩,⟨227,(22),[5,6],[174],1061⟩,⟨227,(23),[1,2,5,6,13,14],[170],788⟩,⟨227,(23),[5,6],[174],1062⟩,⟨227,(24),[1,2,5,6,13,14],[170],787⟩,⟨227,(24),[5,6],[174],1061⟩,⟨228,(0),[1,2,5,6,13,14],[170],789⟩,⟨228,(0),[5,6],[174],789⟩,⟨228,(1),[1,2,5,6,13,14],[170],790⟩,⟨228,(1),[5,6],[174],790⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3712
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3713
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3714
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3715
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3716
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3717
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3718
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3719
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3720
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3721
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3722
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3723
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3724
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3725
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3726
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3727
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3728
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3729
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3730
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3731
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3732
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3733
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3734
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3735
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3736
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3737
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3738
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3739
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3740
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3741
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3742
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3743
end Section14Records_5_3712_3744

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3712_3744


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3744_3776
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3744_3776
private theorem valid3744 : RecordDataValid section14Catalog 5 (⟨228,(2),[1,5,6,13],[170],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3745 : RecordDataValid section14Catalog 5 (⟨228,(2),[5,6],[174],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3746 : RecordDataValid section14Catalog 5 (⟨228,(3),[1,2,5,6,13,14],[170],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3747 : RecordDataValid section14Catalog 5 (⟨228,(3),[5,6],[174],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3748 : RecordDataValid section14Catalog 5 (⟨228,(4),[1,2,5,6,13,14],[170],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3749 : RecordDataValid section14Catalog 5 (⟨228,(4),[5,6],[174],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3750 : RecordDataValid section14Catalog 5 (⟨228,(5),[1,2,5,6,13,14],[170],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3751 : RecordDataValid section14Catalog 5 (⟨228,(5),[5,6],[174],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3752 : RecordDataValid section14Catalog 5 (⟨228,(6),[1,2,5,6,13,14],[170],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3753 : RecordDataValid section14Catalog 5 (⟨228,(6),[5,6],[174],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3754 : RecordDataValid section14Catalog 5 (⟨228,(7),[1,2,5,6,13,14],[170],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3755 : RecordDataValid section14Catalog 5 (⟨228,(7),[5,6],[174],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3756 : RecordDataValid section14Catalog 5 (⟨228,(8),[1,2,5,6,13,14],[170],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3757 : RecordDataValid section14Catalog 5 (⟨228,(8),[5,6],[174],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3758 : RecordDataValid section14Catalog 5 (⟨228,(9),[1,2,5,6,13,14],[170],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3759 : RecordDataValid section14Catalog 5 (⟨228,(9),[5,6],[174],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3760 : RecordDataValid section14Catalog 5 (⟨228,(10),[1,2,5,6,13,14],[170],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3761 : RecordDataValid section14Catalog 5 (⟨228,(10),[5,6],[174],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3762 : RecordDataValid section14Catalog 5 (⟨228,(11),[1,2,5,6,13,14],[170],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3763 : RecordDataValid section14Catalog 5 (⟨228,(11),[5,6],[174],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3764 : RecordDataValid section14Catalog 5 (⟨228,(12),[1,2,5,6,13,14],[170],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3765 : RecordDataValid section14Catalog 5 (⟨228,(12),[5,6],[174],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3766 : RecordDataValid section14Catalog 5 (⟨228,(13),[1,2,5,6,13,14],[170],801⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3767 : RecordDataValid section14Catalog 5 (⟨228,(13),[5,6],[174],801⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3768 : RecordDataValid section14Catalog 5 (⟨228,(14),[1,2,5,6,13,14],[170],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3769 : RecordDataValid section14Catalog 5 (⟨228,(14),[5,6],[174],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3770 : RecordDataValid section14Catalog 5 (⟨228,(15),[1,2,5,6,13,14],[170],802⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3771 : RecordDataValid section14Catalog 5 (⟨228,(15),[5,6],[174],802⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3772 : RecordDataValid section14Catalog 5 (⟨228,(16),[1,2,5,6,13,14],[170],803⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3773 : RecordDataValid section14Catalog 5 (⟨228,(16),[5,6],[174],803⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3774 : RecordDataValid section14Catalog 5 (⟨228,(17),[1,2,5,6,13,14],[170],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3775 : RecordDataValid section14Catalog 5 (⟨228,(17),[5,6],[174],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3744_3776 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3744).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3744).take 32 = [⟨228,(2),[1,5,6,13],[170],791⟩,⟨228,(2),[5,6],[174],791⟩,⟨228,(3),[1,2,5,6,13,14],[170],792⟩,⟨228,(3),[5,6],[174],792⟩,⟨228,(4),[1,2,5,6,13,14],[170],793⟩,⟨228,(4),[5,6],[174],793⟩,⟨228,(5),[1,2,5,6,13,14],[170],794⟩,⟨228,(5),[5,6],[174],794⟩,⟨228,(6),[1,2,5,6,13,14],[170],795⟩,⟨228,(6),[5,6],[174],795⟩,⟨228,(7),[1,2,5,6,13,14],[170],796⟩,⟨228,(7),[5,6],[174],796⟩,⟨228,(8),[1,2,5,6,13,14],[170],797⟩,⟨228,(8),[5,6],[174],797⟩,⟨228,(9),[1,2,5,6,13,14],[170],796⟩,⟨228,(9),[5,6],[174],796⟩,⟨228,(10),[1,2,5,6,13,14],[170],798⟩,⟨228,(10),[5,6],[174],798⟩,⟨228,(11),[1,2,5,6,13,14],[170],799⟩,⟨228,(11),[5,6],[174],799⟩,⟨228,(12),[1,2,5,6,13,14],[170],800⟩,⟨228,(12),[5,6],[174],800⟩,⟨228,(13),[1,2,5,6,13,14],[170],801⟩,⟨228,(13),[5,6],[174],801⟩,⟨228,(14),[1,2,5,6,13,14],[170],800⟩,⟨228,(14),[5,6],[174],800⟩,⟨228,(15),[1,2,5,6,13,14],[170],802⟩,⟨228,(15),[5,6],[174],802⟩,⟨228,(16),[1,2,5,6,13,14],[170],803⟩,⟨228,(16),[5,6],[174],803⟩,⟨228,(17),[1,2,5,6,13,14],[170],804⟩,⟨228,(17),[5,6],[174],804⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3744
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3745
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3746
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3747
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3748
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3749
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3750
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3751
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3752
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3753
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3754
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3755
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3756
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3757
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3758
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3759
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3760
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3761
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3762
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3763
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3764
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3765
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3766
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3767
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3768
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3769
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3770
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3771
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3772
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3773
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3774
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3775
end Section14Records_5_3744_3776

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3744_3776

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3712).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 3712 3744 3776 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_3712_3744 hnum) (Freiman.workReverse20260919_s0005_records_3744_3776 hnum))

#print axioms solution
