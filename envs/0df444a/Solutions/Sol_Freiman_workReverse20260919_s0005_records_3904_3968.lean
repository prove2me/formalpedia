-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3904_3968
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:31:29.404651+00:00
-- url     : https://prove2.me/submissions/26c6d23d-6bf5-435c-ba9d-0c3c46502807

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3904_3936
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3904_3936
private theorem valid3904 : RecordDataValid section14Catalog 5 (⟨232,(12),[1,2,5,6,13,14],[170],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3905 : RecordDataValid section14Catalog 5 (⟨232,(12),[5,6],[174],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3906 : RecordDataValid section14Catalog 5 (⟨232,(13),[1,2,5,6,13,14],[170],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3907 : RecordDataValid section14Catalog 5 (⟨232,(13),[5,6],[174],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3908 : RecordDataValid section14Catalog 5 (⟨232,(14),[1,2,5,6,13,14],[170],855⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨855,[1,2,3,5,6,7,10,11,13,14,15],856⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3909 : RecordDataValid section14Catalog 5 (⟨232,(14),[5,6],[174],1069⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1069,[3,5,6,7],1073⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3910 : RecordDataValid section14Catalog 5 (⟨232,(15),[1,2,5,6,13,14],[170],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3911 : RecordDataValid section14Catalog 5 (⟨232,(15),[5,6],[174],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3912 : RecordDataValid section14Catalog 5 (⟨232,(16),[1,2,5,6,13,14],[170],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3913 : RecordDataValid section14Catalog 5 (⟨232,(16),[5,6],[174],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3914 : RecordDataValid section14Catalog 5 (⟨232,(17),[1,2,5,6,13,14],[170],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3915 : RecordDataValid section14Catalog 5 (⟨232,(17),[5,6],[174],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3916 : RecordDataValid section14Catalog 5 (⟨232,(18),[1,2,5,6,13,14],[170],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3917 : RecordDataValid section14Catalog 5 (⟨232,(18),[5,6],[174],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3918 : RecordDataValid section14Catalog 5 (⟨232,(19),[1,2,5,6,13,14],[170],860⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨860,[1,2,3,5,6,7,10,11,13,14,15],861⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3919 : RecordDataValid section14Catalog 5 (⟨232,(19),[5,6],[174],1071⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1071,[3,5,6,7],1075⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3920 : RecordDataValid section14Catalog 5 (⟨234,(0),[1,2,5,6,13,14],[170],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3921 : RecordDataValid section14Catalog 5 (⟨234,(0),[5,6],[174],1072⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1072,[3,5,6,7],1076⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3922 : RecordDataValid section14Catalog 5 (⟨234,(1),[1,2,5,6,13,14],[170],569⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨569,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],570⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3923 : RecordDataValid section14Catalog 5 (⟨234,(1),[5,6],[174],1073⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1073,[3,5,6,7],1077⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3924 : RecordDataValid section14Catalog 5 (⟨234,(2),[1,2,5,6,13,14],[170],570⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨570,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],571⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3925 : RecordDataValid section14Catalog 5 (⟨234,(2),[5,6],[174],1072⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1072,[3,5,6,7],1076⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3926 : RecordDataValid section14Catalog 5 (⟨234,(3),[1,2,5,6,13,14],[170],571⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨571,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],572⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3927 : RecordDataValid section14Catalog 5 (⟨234,(3),[5,6],[174],1074⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1074,[3,5,6,7],1078⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3928 : RecordDataValid section14Catalog 5 (⟨234,(4),[1,2,5,6,13,14],[170],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3929 : RecordDataValid section14Catalog 5 (⟨234,(4),[5,6],[174],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3930 : RecordDataValid section14Catalog 5 (⟨234,(5),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3931 : RecordDataValid section14Catalog 5 (⟨234,(5),[5,6],[174],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3932 : RecordDataValid section14Catalog 5 (⟨234,(6),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3933 : RecordDataValid section14Catalog 5 (⟨234,(6),[5,6],[174],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3934 : RecordDataValid section14Catalog 5 (⟨234,(7),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3935 : RecordDataValid section14Catalog 5 (⟨234,(7),[5,6],[174],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3904_3936 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3904).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3904).take 32 = [⟨232,(12),[1,2,5,6,13,14],[170],846⟩,⟨232,(12),[5,6],[174],846⟩,⟨232,(13),[1,2,5,6,13,14],[170],847⟩,⟨232,(13),[5,6],[174],847⟩,⟨232,(14),[1,2,5,6,13,14],[170],855⟩,⟨232,(14),[5,6],[174],1069⟩,⟨232,(15),[1,2,5,6,13,14],[170],856⟩,⟨232,(15),[5,6],[174],856⟩,⟨232,(16),[1,2,5,6,13,14],[170],857⟩,⟨232,(16),[5,6],[174],857⟩,⟨232,(17),[1,2,5,6,13,14],[170],858⟩,⟨232,(17),[5,6],[174],858⟩,⟨232,(18),[1,2,5,6,13,14],[170],859⟩,⟨232,(18),[5,6],[174],859⟩,⟨232,(19),[1,2,5,6,13,14],[170],860⟩,⟨232,(19),[5,6],[174],1071⟩,⟨234,(0),[1,2,5,6,13,14],[170],568⟩,⟨234,(0),[5,6],[174],1072⟩,⟨234,(1),[1,2,5,6,13,14],[170],569⟩,⟨234,(1),[5,6],[174],1073⟩,⟨234,(2),[1,2,5,6,13,14],[170],570⟩,⟨234,(2),[5,6],[174],1072⟩,⟨234,(3),[1,2,5,6,13,14],[170],571⟩,⟨234,(3),[5,6],[174],1074⟩,⟨234,(4),[1,2,5,6,13,14],[170],572⟩,⟨234,(4),[5,6],[174],1075⟩,⟨234,(5),[1,2,5,6,13,14],[170],573⟩,⟨234,(5),[5,6],[174],1075⟩,⟨234,(6),[1,2,5,6,13,14],[170],573⟩,⟨234,(6),[5,6],[174],1075⟩,⟨234,(7),[1,2,5,6,13,14],[170],573⟩,⟨234,(7),[5,6],[174],1075⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3904
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3905
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3906
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3907
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3908
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3909
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3910
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3911
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3912
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3913
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3914
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3915
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3916
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3917
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3918
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3919
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3920
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3921
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3922
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3923
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3924
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3925
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3926
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3927
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3928
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3929
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3930
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3931
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3932
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3933
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3934
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3935
end Section14Records_5_3904_3936

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3904_3936


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3936_3968
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3936_3968
private theorem valid3936 : RecordDataValid section14Catalog 5 (⟨234,(8),[1,2,5,6,13,14],[170],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3937 : RecordDataValid section14Catalog 5 (⟨234,(8),[5,6],[174],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3938 : RecordDataValid section14Catalog 5 (⟨234,(9),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3939 : RecordDataValid section14Catalog 5 (⟨234,(9),[5,6],[174],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3940 : RecordDataValid section14Catalog 5 (⟨234,(10),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3941 : RecordDataValid section14Catalog 5 (⟨234,(10),[5,6],[174],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3942 : RecordDataValid section14Catalog 5 (⟨234,(11),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3943 : RecordDataValid section14Catalog 5 (⟨234,(11),[5,6],[174],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3944 : RecordDataValid section14Catalog 5 (⟨234,(12),[1,2,5,6,13,14],[170],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3945 : RecordDataValid section14Catalog 5 (⟨234,(12),[5,6],[174],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3946 : RecordDataValid section14Catalog 5 (⟨234,(13),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3947 : RecordDataValid section14Catalog 5 (⟨234,(13),[5,6],[174],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3948 : RecordDataValid section14Catalog 5 (⟨234,(14),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3949 : RecordDataValid section14Catalog 5 (⟨234,(14),[5,6],[174],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3950 : RecordDataValid section14Catalog 5 (⟨234,(15),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3951 : RecordDataValid section14Catalog 5 (⟨234,(15),[5,6],[174],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3952 : RecordDataValid section14Catalog 5 (⟨235,(0),[1,2,5,6,13,14],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3953 : RecordDataValid section14Catalog 5 (⟨235,(0),[5,6],[174],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3954 : RecordDataValid section14Catalog 5 (⟨235,(1),[1,2,5,6,13,14],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3955 : RecordDataValid section14Catalog 5 (⟨235,(1),[5,6],[174],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3956 : RecordDataValid section14Catalog 5 (⟨235,(2),[1,2,5,6,13,14],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3957 : RecordDataValid section14Catalog 5 (⟨235,(2),[5,6],[174],1078⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1078,[3,5,6,7],1082⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3958 : RecordDataValid section14Catalog 5 (⟨235,(3),[1,2,5,6,13,14],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3959 : RecordDataValid section14Catalog 5 (⟨235,(3),[5,6],[174],1079⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1079,[3,5,6,7],1083⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3960 : RecordDataValid section14Catalog 5 (⟨235,(4),[1,2,5,6,13,14],[170],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3961 : RecordDataValid section14Catalog 5 (⟨235,(4),[5,6],[174],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3962 : RecordDataValid section14Catalog 5 (⟨235,(5),[1,2,5,6,13,14],[170],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3963 : RecordDataValid section14Catalog 5 (⟨235,(5),[5,6],[174],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3964 : RecordDataValid section14Catalog 5 (⟨235,(6),[1,2,5,6,13,14],[170],584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3965 : RecordDataValid section14Catalog 5 (⟨235,(6),[5,6],[174],1080⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1080,[3,5,6,7],1084⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3966 : RecordDataValid section14Catalog 5 (⟨235,(7),[1,2,5,6,13,14],[170],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3967 : RecordDataValid section14Catalog 5 (⟨235,(7),[5,6],[174],1081⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1081,[3,5,6,7],1085⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3936_3968 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3936).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3936).take 32 = [⟨234,(8),[1,2,5,6,13,14],[170],574⟩,⟨234,(8),[5,6],[174],1076⟩,⟨234,(9),[1,2,5,6,13,14],[170],575⟩,⟨234,(9),[5,6],[174],1076⟩,⟨234,(10),[1,2,5,6,13,14],[170],575⟩,⟨234,(10),[5,6],[174],1076⟩,⟨234,(11),[1,2,5,6,13,14],[170],575⟩,⟨234,(11),[5,6],[174],1076⟩,⟨234,(12),[1,2,5,6,13,14],[170],576⟩,⟨234,(12),[5,6],[174],1077⟩,⟨234,(13),[1,2,5,6,13,14],[170],577⟩,⟨234,(13),[5,6],[174],1077⟩,⟨234,(14),[1,2,5,6,13,14],[170],577⟩,⟨234,(14),[5,6],[174],1077⟩,⟨234,(15),[1,2,5,6,13,14],[170],577⟩,⟨234,(15),[5,6],[174],1077⟩,⟨235,(0),[1,2,5,6,13,14],[170],578⟩,⟨235,(0),[5,6],[174],578⟩,⟨235,(1),[1,2,5,6,13,14],[170],579⟩,⟨235,(1),[5,6],[174],579⟩,⟨235,(2),[1,2,5,6,13,14],[170],580⟩,⟨235,(2),[5,6],[174],1078⟩,⟨235,(3),[1,2,5,6,13,14],[170],581⟩,⟨235,(3),[5,6],[174],1079⟩,⟨235,(4),[1,2,5,6,13,14],[170],582⟩,⟨235,(4),[5,6],[174],582⟩,⟨235,(5),[1,2,5,6,13,14],[170],583⟩,⟨235,(5),[5,6],[174],583⟩,⟨235,(6),[1,2,5,6,13,14],[170],584⟩,⟨235,(6),[5,6],[174],1080⟩,⟨235,(7),[1,2,5,6,13,14],[170],585⟩,⟨235,(7),[5,6],[174],1081⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3936
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3937
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3938
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3939
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3940
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3941
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3942
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3943
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3944
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3945
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3946
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3947
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3948
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3949
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3950
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3951
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3952
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3953
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3954
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3955
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3956
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3957
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3958
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3959
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3960
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3961
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3962
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3963
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3964
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3965
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3966
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3967
end Section14Records_5_3936_3968

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3936_3968

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3904).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 3904 3936 3968 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_3904_3936 hnum) (Freiman.workReverse20260919_s0005_records_3936_3968 hnum))

#print axioms solution
