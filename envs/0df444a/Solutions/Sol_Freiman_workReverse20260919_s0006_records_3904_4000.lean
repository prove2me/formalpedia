-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3904_4000
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:34:36.116325+00:00
-- url     : https://prove2.me/submissions/b8930c00-2ceb-4f51-b545-699cb217e5f9

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3904_3936
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3904_3936
private theorem valid3904 : RecordDataValid section14Catalog 6 (⟨249,(19),[1,2,5,6,13,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3905 : RecordDataValid section14Catalog 6 (⟨249,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3906 : RecordDataValid section14Catalog 6 (⟨249,(21),[2,5,6,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3907 : RecordDataValid section14Catalog 6 (⟨249,(22),[1,2,5,6,13,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3908 : RecordDataValid section14Catalog 6 (⟨249,(23),[1,2,5,6,13,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3909 : RecordDataValid section14Catalog 6 (⟨249,(24),[1,2,5,6,13,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3910 : RecordDataValid section14Catalog 6 (⟨253,(0),[1,2,5,6,13,14],[170],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3911 : RecordDataValid section14Catalog 6 (⟨253,(1),[1,2,5,6,13,14],[170],894⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3912 : RecordDataValid section14Catalog 6 (⟨253,(2),[1,2,5,6,13,14],[170],895⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨895,[1,2,3,4,5,6,7,8,9,10,13,14,16],897⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3913 : RecordDataValid section14Catalog 6 (⟨253,(3),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3914 : RecordDataValid section14Catalog 6 (⟨253,(4),[1,2,5,6,13,14],[170],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3915 : RecordDataValid section14Catalog 6 (⟨253,(5),[1,2,5,6,13,14],[170],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3916 : RecordDataValid section14Catalog 6 (⟨253,(6),[1,2,5,6,13,14],[170],894⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3917 : RecordDataValid section14Catalog 6 (⟨253,(7),[1,2,5,6,13,14],[170],896⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨896,[1,2,4,5,6,10,13,14,16],898⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3918 : RecordDataValid section14Catalog 6 (⟨253,(8),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3919 : RecordDataValid section14Catalog 6 (⟨253,(9),[1,2,5,6,13,14],[170],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3920 : RecordDataValid section14Catalog 6 (⟨253,(10),[1,2,5,6,13,14],[170],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3921 : RecordDataValid section14Catalog 6 (⟨253,(11),[1,2,5,6,13,14],[170],897⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨897,[1,2,4,5,6,8,9,10,12,13,14,16],899⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3922 : RecordDataValid section14Catalog 6 (⟨253,(12),[1,2,5,6,13,14],[170],898⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨898,[1,2,4,5,6,8,9,10,12,13,14,16],900⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3923 : RecordDataValid section14Catalog 6 (⟨253,(13),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3924 : RecordDataValid section14Catalog 6 (⟨253,(14),[1,2,5,6,13,14],[170],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3925 : RecordDataValid section14Catalog 6 (⟨253,(15),[1,2,5,6,13,14],[170],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3926 : RecordDataValid section14Catalog 6 (⟨253,(16),[1,2,5,6,13,14],[170],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3927 : RecordDataValid section14Catalog 6 (⟨253,(17),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3928 : RecordDataValid section14Catalog 6 (⟨253,(18),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3929 : RecordDataValid section14Catalog 6 (⟨253,(19),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3930 : RecordDataValid section14Catalog 6 (⟨253,(20),[1,2,5,6,13,14],[170],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3931 : RecordDataValid section14Catalog 6 (⟨253,(21),[1,2,5,6,13,14],[170],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3932 : RecordDataValid section14Catalog 6 (⟨253,(22),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3933 : RecordDataValid section14Catalog 6 (⟨253,(23),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3934 : RecordDataValid section14Catalog 6 (⟨253,(24),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3935 : RecordDataValid section14Catalog 6 (⟨255,(0),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3904_3936 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3904).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3904).take 32 = [⟨249,(19),[1,2,5,6,13,14],[170],892⟩,⟨249,(20),[1,2,5,6,13,14],[170],24⟩,⟨249,(21),[2,5,6,14],[170],893⟩,⟨249,(22),[1,2,5,6,13,14],[170],893⟩,⟨249,(23),[1,2,5,6,13,14],[170],893⟩,⟨249,(24),[1,2,5,6,13,14],[170],893⟩,⟨253,(0),[1,2,5,6,13,14],[170],884⟩,⟨253,(1),[1,2,5,6,13,14],[170],894⟩,⟨253,(2),[1,2,5,6,13,14],[170],895⟩,⟨253,(3),[1,2,5,6,13,14],[170],29⟩,⟨253,(4),[1,2,5,6,13,14],[170],30⟩,⟨253,(5),[1,2,5,6,13,14],[170],884⟩,⟨253,(6),[1,2,5,6,13,14],[170],894⟩,⟨253,(7),[1,2,5,6,13,14],[170],896⟩,⟨253,(8),[1,2,5,6,13,14],[170],29⟩,⟨253,(9),[1,2,5,6,13,14],[170],32⟩,⟨253,(10),[1,2,5,6,13,14],[170],84⟩,⟨253,(11),[1,2,5,6,13,14],[170],897⟩,⟨253,(12),[1,2,5,6,13,14],[170],898⟩,⟨253,(13),[1,2,5,6,13,14],[170],29⟩,⟨253,(14),[1,2,5,6,13,14],[170],34⟩,⟨253,(15),[1,2,5,6,13,14],[170],35⟩,⟨253,(16),[1,2,5,6,13,14],[170],36⟩,⟨253,(17),[1,2,5,6,13,14],[170],37⟩,⟨253,(18),[1,2,5,6,13,14],[170],29⟩,⟨253,(19),[1,2,5,6,13,14],[170],37⟩,⟨253,(20),[1,2,5,6,13,14],[170],38⟩,⟨253,(21),[1,2,5,6,13,14],[170],39⟩,⟨253,(22),[1,2,5,6,13,14],[170],40⟩,⟨253,(23),[1,2,5,6,13,14],[170],29⟩,⟨253,(24),[1,2,5,6,13,14],[170],40⟩,⟨255,(0),[1,2,5,6],[170],899⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3904
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3905
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3906
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3907
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3908
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3909
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3910
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3911
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3912
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3913
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3914
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3915
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3916
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3917
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3918
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3919
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3920
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3921
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3922
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3923
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3924
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3925
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3926
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3927
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3928
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3929
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3930
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3931
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3932
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3933
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3934
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3935
end Section14Records_6_3904_3936

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3904_3936


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3936_3968
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3936_3968
private theorem valid3936 : RecordDataValid section14Catalog 6 (⟨255,(1),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3937 : RecordDataValid section14Catalog 6 (⟨255,(2),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3938 : RecordDataValid section14Catalog 6 (⟨255,(3),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3939 : RecordDataValid section14Catalog 6 (⟨255,(4),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3940 : RecordDataValid section14Catalog 6 (⟨255,(5),[1,2,5,6],[170],903⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨903,[1,2,4,5,6,8],905⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3941 : RecordDataValid section14Catalog 6 (⟨255,(6),[1,2,5,6],[170],903⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨903,[1,2,4,5,6,8],905⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3942 : RecordDataValid section14Catalog 6 (⟨255,(7),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3943 : RecordDataValid section14Catalog 6 (⟨255,(8),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3944 : RecordDataValid section14Catalog 6 (⟨255,(9),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3945 : RecordDataValid section14Catalog 6 (⟨255,(10),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3946 : RecordDataValid section14Catalog 6 (⟨255,(11),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3947 : RecordDataValid section14Catalog 6 (⟨255,(12),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3948 : RecordDataValid section14Catalog 6 (⟨255,(13),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3949 : RecordDataValid section14Catalog 6 (⟨255,(14),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3950 : RecordDataValid section14Catalog 6 (⟨255,(15),[1,2,5,6],[170],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3951 : RecordDataValid section14Catalog 6 (⟨255,(16),[1,2,5,6],[170],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3952 : RecordDataValid section14Catalog 6 (⟨255,(17),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3953 : RecordDataValid section14Catalog 6 (⟨255,(18),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3954 : RecordDataValid section14Catalog 6 (⟨255,(19),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3955 : RecordDataValid section14Catalog 6 (⟨255,(20),[1,2,5,6],[170],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3956 : RecordDataValid section14Catalog 6 (⟨255,(21),[1,2,5,6],[170],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3957 : RecordDataValid section14Catalog 6 (⟨255,(22),[1,2,5,6],[170],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3958 : RecordDataValid section14Catalog 6 (⟨255,(23),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3959 : RecordDataValid section14Catalog 6 (⟨255,(24),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3960 : RecordDataValid section14Catalog 6 (⟨258,(5),[6,13],[170],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3961 : RecordDataValid section14Catalog 6 (⟨258,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3962 : RecordDataValid section14Catalog 6 (⟨258,(8),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3963 : RecordDataValid section14Catalog 6 (⟨258,(9),[5,6,13,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3964 : RecordDataValid section14Catalog 6 (⟨258,(15),[1,2,6,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3965 : RecordDataValid section14Catalog 6 (⟨258,(16),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3966 : RecordDataValid section14Catalog 6 (⟨258,(17),[1,2,5,6,13,14],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3967 : RecordDataValid section14Catalog 6 (⟨258,(19),[2,5,6,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3936_3968 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3936).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3936).take 32 = [⟨255,(1),[1,2,5,6],[170],899⟩,⟨255,(2),[1,2,5,6],[170],900⟩,⟨255,(3),[1,2,5,6],[170],901⟩,⟨255,(4),[1,2,5,6],[170],902⟩,⟨255,(5),[1,2,5,6],[170],903⟩,⟨255,(6),[1,2,5,6],[170],903⟩,⟨255,(7),[1,2,5,6],[170],900⟩,⟨255,(8),[1,2,5,6],[170],901⟩,⟨255,(9),[1,2,5,6],[170],902⟩,⟨255,(10),[1,2,5,6],[170],899⟩,⟨255,(11),[1,2,5,6],[170],899⟩,⟨255,(12),[1,2,5,6],[170],900⟩,⟨255,(13),[1,2,5,6],[170],901⟩,⟨255,(14),[1,2,5,6],[170],902⟩,⟨255,(15),[1,2,5,6],[170],904⟩,⟨255,(16),[1,2,5,6],[170],904⟩,⟨255,(17),[1,2,5,6],[170],900⟩,⟨255,(18),[1,2,5,6],[170],901⟩,⟨255,(19),[1,2,5,6],[170],902⟩,⟨255,(20),[1,2,5,6],[170],905⟩,⟨255,(21),[1,2,5,6],[170],905⟩,⟨255,(22),[1,2,5,6],[170],905⟩,⟨255,(23),[1,2,5,6],[170],901⟩,⟨255,(24),[1,2,5,6],[170],902⟩,⟨258,(5),[6,13],[170],105⟩,⟨258,(7),[1,2,5,6,13,14],[170],3⟩,⟨258,(8),[1,5,6,13,14],[170],3⟩,⟨258,(9),[5,6,13,14],[170],143⟩,⟨258,(15),[1,2,6,14],[170],3⟩,⟨258,(16),[1,5,6,13,14],[170],3⟩,⟨258,(17),[1,2,5,6,13,14],[170],48⟩,⟨258,(19),[2,5,6,14],[170],143⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3936
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3937
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3938
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3939
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3940
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3941
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3942
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3943
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3944
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3945
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3946
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3947
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3948
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3949
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3950
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3951
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3952
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3953
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3954
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3955
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3956
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3957
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3958
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3959
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3960
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3961
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3962
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3963
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3964
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3965
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3966
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3967
end Section14Records_6_3936_3968

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3936_3968


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3968_4000
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3968_4000
private theorem valid3968 : RecordDataValid section14Catalog 6 (⟨259,(1),[1,2,5,6],[170],906⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨906,[1,2,4,5,6,8,9,10,12],908⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3969 : RecordDataValid section14Catalog 6 (⟨259,(3),[1,2,5,6],[170],907⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨907,[1,2,4,5,6,8,9,10,12],909⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3970 : RecordDataValid section14Catalog 6 (⟨259,(5),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3971 : RecordDataValid section14Catalog 6 (⟨259,(7),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3972 : RecordDataValid section14Catalog 6 (⟨259,(11),[2,5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3973 : RecordDataValid section14Catalog 6 (⟨259,(13),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3974 : RecordDataValid section14Catalog 6 (⟨259,(15),[1,6],[170],53⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨53,[1,4,6,8,9,10],53⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3975 : RecordDataValid section14Catalog 6 (⟨259,(17),[2,5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3976 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3977 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3978 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3979 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3980 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3981 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3982 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3983 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[130,134],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3984 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[146],885⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨885,[1,2,3,5,6,7,13,14,15],887⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3985 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3986 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[150],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3987 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[174],908⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨908,[1,2,3,5,6,7,13,14,15],910⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3988 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[186],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3989 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3990 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3991 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,5,6,14],[190],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3992 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,2,6,13,14],[170],911⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨911,[6,10],914⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3993 : RecordDataValid section14Catalog 6 (⟨260,(-1),[1,5,6,13],[194,198],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3994 : RecordDataValid section14Catalog 6 (⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3995 : RecordDataValid section14Catalog 6 (⟨260,(-1),[2,6,9,10,14],[16,20],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3996 : RecordDataValid section14Catalog 6 (⟨260,(-1),[2,6,14],[40,44,56,60],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3997 : RecordDataValid section14Catalog 6 (⟨260,(-1),[2,6,14],[211,215,235,239,251,255],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3998 : RecordDataValid section14Catalog 6 (⟨260,(-1),[5,6],[131,135],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3999 : RecordDataValid section14Catalog 6 (⟨260,(-1),[6],[195,199],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3968_4000 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3968).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3968).take 32 = [⟨259,(1),[1,2,5,6],[170],906⟩,⟨259,(3),[1,2,5,6],[170],907⟩,⟨259,(5),[5,6],[170],143⟩,⟨259,(7),[5,6],[170],143⟩,⟨259,(11),[2,5,6],[170],143⟩,⟨259,(13),[5,6],[170],143⟩,⟨259,(15),[1,6],[170],53⟩,⟨259,(17),[2,5,6],[170],143⟩,⟨260,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨260,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩,⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨260,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩,⟨260,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩,⟨260,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩,⟨260,(-1),[1,2,5,6,13,14],[130,134],884⟩,⟨260,(-1),[1,2,5,6,13,14],[146],885⟩,⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩,⟨260,(-1),[1,2,5,6,13,14],[150],887⟩,⟨260,(-1),[1,2,5,6,13,14],[174],908⟩,⟨260,(-1),[1,2,5,6,13,14],[186],909⟩,⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩,⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨260,(-1),[1,2,5,6,14],[190],909⟩,⟨260,(-1),[1,2,6,13,14],[170],911⟩,⟨260,(-1),[1,5,6,13],[194,198],910⟩,⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩,⟨260,(-1),[2,6,9,10,14],[16,20],882⟩,⟨260,(-1),[2,6,14],[40,44,56,60],882⟩,⟨260,(-1),[2,6,14],[211,215,235,239,251,255],886⟩,⟨260,(-1),[5,6],[131,135],886⟩,⟨260,(-1),[6],[195,199],886⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3968
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3969
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3970
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3971
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3972
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3973
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3974
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3975
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3976
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3977
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3978
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3979
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3980
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3981
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3982
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3983
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3984
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3985
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3986
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3987
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3988
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3989
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3990
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3991
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3992
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3993
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3994
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3995
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3996
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3997
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3998
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3999
end Section14Records_6_3968_4000

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3968_4000

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3904).take 96, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 3904 3936 4000 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3904_3936 hnum) (all_of_interval_split P xs 3936 3968 4000 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3936_3968 hnum) (Freiman.workReverse20260919_s0006_records_3968_4000 hnum)))

#print axioms solution
