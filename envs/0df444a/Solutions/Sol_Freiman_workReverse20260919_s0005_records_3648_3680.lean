-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3648_3680
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:03:55.853606+00:00
-- url     : https://prove2.me/submissions/a234708c-48bb-4a51-8987-7e4969047991

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
namespace Section14Records_5_3648_3680
private theorem valid3648 : RecordDataValid section14Catalog 5 (⟨225,(14),[1,2,5,6,13,14],[170],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3649 : RecordDataValid section14Catalog 5 (⟨225,(14),[5,6],[174],1053⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1053,[3,5,6,7],1057⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3650 : RecordDataValid section14Catalog 5 (⟨225,(15),[1,2,5,6,13,14],[170],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3651 : RecordDataValid section14Catalog 5 (⟨225,(15),[5,6],[174],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3652 : RecordDataValid section14Catalog 5 (⟨225,(16),[1,2,5,6,13,14],[170],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3653 : RecordDataValid section14Catalog 5 (⟨225,(16),[5,6],[174],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3654 : RecordDataValid section14Catalog 5 (⟨225,(17),[1,2,5,6,13,14],[170],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3655 : RecordDataValid section14Catalog 5 (⟨225,(17),[5,6],[174],1054⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1054,[3,5,6,7],1058⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3656 : RecordDataValid section14Catalog 5 (⟨225,(18),[1,2,5,6,13,14],[170],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3657 : RecordDataValid section14Catalog 5 (⟨225,(18),[5,6],[174],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3658 : RecordDataValid section14Catalog 5 (⟨225,(19),[1,2,5,6,13,14],[170],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3659 : RecordDataValid section14Catalog 5 (⟨225,(19),[5,6],[174],1054⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1054,[3,5,6,7],1058⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3660 : RecordDataValid section14Catalog 5 (⟨225,(20),[1,2,5,6,13,14],[170],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3661 : RecordDataValid section14Catalog 5 (⟨225,(20),[5,6],[174],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3662 : RecordDataValid section14Catalog 5 (⟨225,(21),[1,2,5,6,13,14],[170],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3663 : RecordDataValid section14Catalog 5 (⟨225,(21),[5,6],[174],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3664 : RecordDataValid section14Catalog 5 (⟨225,(22),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3665 : RecordDataValid section14Catalog 5 (⟨225,(22),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3666 : RecordDataValid section14Catalog 5 (⟨225,(23),[1,2,5,6,13,14],[170],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3667 : RecordDataValid section14Catalog 5 (⟨225,(23),[5,6],[174],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3668 : RecordDataValid section14Catalog 5 (⟨225,(24),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3669 : RecordDataValid section14Catalog 5 (⟨225,(24),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3670 : RecordDataValid section14Catalog 5 (⟨226,(0),[1,2,5,6,13,14],[170],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3671 : RecordDataValid section14Catalog 5 (⟨226,(0),[5,6],[174],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3672 : RecordDataValid section14Catalog 5 (⟨226,(1),[1,2,5,6,13,14],[170],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3673 : RecordDataValid section14Catalog 5 (⟨226,(1),[5,6],[174],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3674 : RecordDataValid section14Catalog 5 (⟨226,(2),[1,2,5,6,13,14],[170],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3675 : RecordDataValid section14Catalog 5 (⟨226,(2),[5,6],[174],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3676 : RecordDataValid section14Catalog 5 (⟨226,(3),[1,2,5,6,13,14],[170],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3677 : RecordDataValid section14Catalog 5 (⟨226,(3),[5,6],[174],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3678 : RecordDataValid section14Catalog 5 (⟨226,(4),[1,2,5,6,13,14],[170],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3679 : RecordDataValid section14Catalog 5 (⟨226,(4),[5,6],[174],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3648).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3648).take 32 = [⟨225,(14),[1,2,5,6,13,14],[170],757⟩,⟨225,(14),[5,6],[174],1053⟩,⟨225,(15),[1,2,5,6,13,14],[170],759⟩,⟨225,(15),[5,6],[174],759⟩,⟨225,(16),[1,2,5,6,13,14],[170],760⟩,⟨225,(16),[5,6],[174],760⟩,⟨225,(17),[1,2,5,6,13,14],[170],761⟩,⟨225,(17),[5,6],[174],1054⟩,⟨225,(18),[1,2,5,6,13,14],[170],762⟩,⟨225,(18),[5,6],[174],762⟩,⟨225,(19),[1,2,5,6,13,14],[170],761⟩,⟨225,(19),[5,6],[174],1054⟩,⟨225,(20),[1,2,5,6,13,14],[170],763⟩,⟨225,(20),[5,6],[174],763⟩,⟨225,(21),[1,2,5,6,13,14],[170],764⟩,⟨225,(21),[5,6],[174],764⟩,⟨225,(22),[1,2,5,6,13,14],[170],547⟩,⟨225,(22),[5,6],[174],1048⟩,⟨225,(23),[1,2,5,6,13,14],[170],765⟩,⟨225,(23),[5,6],[174],765⟩,⟨225,(24),[1,2,5,6,13,14],[170],547⟩,⟨225,(24),[5,6],[174],1048⟩,⟨226,(0),[1,2,5,6,13,14],[170],766⟩,⟨226,(0),[5,6],[174],766⟩,⟨226,(1),[1,2,5,6,13,14],[170],767⟩,⟨226,(1),[5,6],[174],767⟩,⟨226,(2),[1,2,5,6,13,14],[170],768⟩,⟨226,(2),[5,6],[174],768⟩,⟨226,(3),[1,2,5,6,13,14],[170],767⟩,⟨226,(3),[5,6],[174],767⟩,⟨226,(4),[1,2,5,6,13,14],[170],769⟩,⟨226,(4),[5,6],[174],769⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3648
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3649
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3650
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3651
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3652
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3653
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3654
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3655
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3656
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3657
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3658
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3659
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3660
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3661
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3662
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3663
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3664
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3665
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3666
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3667
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3668
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3669
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3670
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3671
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3672
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3673
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3674
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3675
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3676
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3677
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3678
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3679
end Section14Records_5_3648_3680

#print axioms solution
