-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3648_3680
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:50:39.821924+00:00
-- url     : https://prove2.me/submissions/4df1f1dc-5ffe-4ad5-82ab-e92fe9f33f34

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
namespace Section14Records_6_3648_3680
private theorem valid3648 : RecordDataValid section14Catalog 6 (⟨234,(6),[5,6],[174],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3649 : RecordDataValid section14Catalog 6 (⟨234,(7),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3650 : RecordDataValid section14Catalog 6 (⟨234,(7),[5,6],[174],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3651 : RecordDataValid section14Catalog 6 (⟨234,(8),[1,2,5,6,13,14],[170],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3652 : RecordDataValid section14Catalog 6 (⟨234,(8),[5,6],[174],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3653 : RecordDataValid section14Catalog 6 (⟨234,(9),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3654 : RecordDataValid section14Catalog 6 (⟨234,(9),[5,6],[174],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3655 : RecordDataValid section14Catalog 6 (⟨234,(10),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3656 : RecordDataValid section14Catalog 6 (⟨234,(10),[5,6],[174],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3657 : RecordDataValid section14Catalog 6 (⟨234,(11),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3658 : RecordDataValid section14Catalog 6 (⟨234,(11),[5,6],[174],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3659 : RecordDataValid section14Catalog 6 (⟨234,(12),[1,2,5,6,13,14],[170],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3660 : RecordDataValid section14Catalog 6 (⟨234,(12),[5,6],[174],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3661 : RecordDataValid section14Catalog 6 (⟨234,(13),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3662 : RecordDataValid section14Catalog 6 (⟨234,(13),[5,6],[174],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3663 : RecordDataValid section14Catalog 6 (⟨234,(14),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3664 : RecordDataValid section14Catalog 6 (⟨234,(14),[5,6],[174],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3665 : RecordDataValid section14Catalog 6 (⟨234,(15),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3666 : RecordDataValid section14Catalog 6 (⟨234,(15),[5,6],[174],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3667 : RecordDataValid section14Catalog 6 (⟨235,(0),[1,2,5,6,13,14],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3668 : RecordDataValid section14Catalog 6 (⟨235,(0),[5,6],[174],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3669 : RecordDataValid section14Catalog 6 (⟨235,(1),[1,2,5,6,13,14],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3670 : RecordDataValid section14Catalog 6 (⟨235,(1),[5,6],[174],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3671 : RecordDataValid section14Catalog 6 (⟨235,(2),[1,2,5,6,13,14],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3672 : RecordDataValid section14Catalog 6 (⟨235,(2),[5,6],[174],1078⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1078,[3,5,6,7],1082⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3673 : RecordDataValid section14Catalog 6 (⟨235,(3),[1,2,5,6,13,14],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3674 : RecordDataValid section14Catalog 6 (⟨235,(3),[5,6],[174],1079⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1079,[3,5,6,7],1083⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3675 : RecordDataValid section14Catalog 6 (⟨235,(4),[1,2,5,6,13,14],[170],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3676 : RecordDataValid section14Catalog 6 (⟨235,(4),[5,6],[174],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3677 : RecordDataValid section14Catalog 6 (⟨235,(5),[1,2,5,6,13,14],[170],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3678 : RecordDataValid section14Catalog 6 (⟨235,(5),[5,6],[174],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3679 : RecordDataValid section14Catalog 6 (⟨235,(6),[1,2,5,6,13,14],[170],584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3648).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3648).take 32 = [⟨234,(6),[5,6],[174],1075⟩,⟨234,(7),[1,2,5,6,13,14],[170],573⟩,⟨234,(7),[5,6],[174],1075⟩,⟨234,(8),[1,2,5,6,13,14],[170],574⟩,⟨234,(8),[5,6],[174],1076⟩,⟨234,(9),[1,2,5,6,13,14],[170],575⟩,⟨234,(9),[5,6],[174],1076⟩,⟨234,(10),[1,2,5,6,13,14],[170],575⟩,⟨234,(10),[5,6],[174],1076⟩,⟨234,(11),[1,2,5,6,13,14],[170],575⟩,⟨234,(11),[5,6],[174],1076⟩,⟨234,(12),[1,2,5,6,13,14],[170],576⟩,⟨234,(12),[5,6],[174],1077⟩,⟨234,(13),[1,2,5,6,13,14],[170],577⟩,⟨234,(13),[5,6],[174],1077⟩,⟨234,(14),[1,2,5,6,13,14],[170],577⟩,⟨234,(14),[5,6],[174],1077⟩,⟨234,(15),[1,2,5,6,13,14],[170],577⟩,⟨234,(15),[5,6],[174],1077⟩,⟨235,(0),[1,2,5,6,13,14],[170],578⟩,⟨235,(0),[5,6],[174],578⟩,⟨235,(1),[1,2,5,6,13,14],[170],579⟩,⟨235,(1),[5,6],[174],579⟩,⟨235,(2),[1,2,5,6,13,14],[170],580⟩,⟨235,(2),[5,6],[174],1078⟩,⟨235,(3),[1,2,5,6,13,14],[170],581⟩,⟨235,(3),[5,6],[174],1079⟩,⟨235,(4),[1,2,5,6,13,14],[170],582⟩,⟨235,(4),[5,6],[174],582⟩,⟨235,(5),[1,2,5,6,13,14],[170],583⟩,⟨235,(5),[5,6],[174],583⟩,⟨235,(6),[1,2,5,6,13,14],[170],584⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3648
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3649
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3650
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3651
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3652
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3653
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3654
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3655
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3656
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3657
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3658
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3659
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3660
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3661
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3662
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3663
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3664
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3665
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3666
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3667
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3668
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3669
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3670
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3671
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3672
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3673
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3674
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3675
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3676
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3677
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3678
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3679
end Section14Records_6_3648_3680

#print axioms solution
