-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3744_3776
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:51:31.551459+00:00
-- url     : https://prove2.me/submissions/affee89d-3357-448a-9b71-6268a65d4846

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
namespace Section14Records_6_3744_3776
private theorem valid3744 : RecordDataValid section14Catalog 6 (⟨238,(2),[5,6],[174],1084⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1084,[3,5,6,7],1088⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3745 : RecordDataValid section14Catalog 6 (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3746 : RecordDataValid section14Catalog 6 (⟨238,(3),[5,6],[174],1085⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1085,[3,5,6],1089⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3747 : RecordDataValid section14Catalog 6 (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3748 : RecordDataValid section14Catalog 6 (⟨238,(4),[5,6],[174],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3749 : RecordDataValid section14Catalog 6 (⟨238,(5),[1,2,5,6,13,14],[170],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3750 : RecordDataValid section14Catalog 6 (⟨238,(5),[5,6],[174],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3751 : RecordDataValid section14Catalog 6 (⟨238,(6),[1,2,5,6,13,14],[170],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3752 : RecordDataValid section14Catalog 6 (⟨238,(6),[5,6],[174],298⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨298,[1,2,3,5,6,7,13,14,15],299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3753 : RecordDataValid section14Catalog 6 (⟨238,(7),[1,2,5,6,13,14],[170],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3754 : RecordDataValid section14Catalog 6 (⟨238,(7),[5,6],[174],298⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨298,[1,2,3,5,6,7,13,14,15],299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3755 : RecordDataValid section14Catalog 6 (⟨238,(8),[1,2,5,6,13,14],[170],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3756 : RecordDataValid section14Catalog 6 (⟨238,(8),[5,6],[174],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3757 : RecordDataValid section14Catalog 6 (⟨238,(9),[1,2,5,6,13,14],[170],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3758 : RecordDataValid section14Catalog 6 (⟨238,(9),[5,6],[174],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3759 : RecordDataValid section14Catalog 6 (⟨238,(10),[1,2,5,6,13,14],[170],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3760 : RecordDataValid section14Catalog 6 (⟨238,(10),[5,6],[174],299⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨299,[1,2,3,5,6,7,13,14,15],300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3761 : RecordDataValid section14Catalog 6 (⟨238,(11),[1,2,5,6,13,14],[170],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3762 : RecordDataValid section14Catalog 6 (⟨238,(11),[5,6],[174],299⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨299,[1,2,3,5,6,7,13,14,15],300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3763 : RecordDataValid section14Catalog 6 (⟨238,(12),[1,2,5,6,13,14],[170],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3764 : RecordDataValid section14Catalog 6 (⟨238,(12),[5,6],[174],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3765 : RecordDataValid section14Catalog 6 (⟨238,(13),[1,2,5,6,13,14],[170],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3766 : RecordDataValid section14Catalog 6 (⟨238,(13),[5,6],[174],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3767 : RecordDataValid section14Catalog 6 (⟨238,(14),[1,2,5,6,13,14],[170],619⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3768 : RecordDataValid section14Catalog 6 (⟨238,(14),[5,6],[174],300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨300,[1,2,3,5,6,7,13,14,15],301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3769 : RecordDataValid section14Catalog 6 (⟨238,(15),[1,2,5,6,13,14],[170],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3770 : RecordDataValid section14Catalog 6 (⟨238,(15),[5,6],[174],300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨300,[1,2,3,5,6,7,13,14,15],301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3771 : RecordDataValid section14Catalog 6 (⟨242,(0),[1,2,5,6],[170],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3772 : RecordDataValid section14Catalog 6 (⟨242,(0),[5,6],[174],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3773 : RecordDataValid section14Catalog 6 (⟨242,(1),[1,2,5,6],[170],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3774 : RecordDataValid section14Catalog 6 (⟨242,(1),[5,6],[174],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3775 : RecordDataValid section14Catalog 6 (⟨242,(2),[1,2,5,6],[170],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3744).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3744).take 32 = [⟨238,(2),[5,6],[174],1084⟩,⟨238,(3),[1,2,5,6,13,14],[170],871⟩,⟨238,(3),[5,6],[174],1085⟩,⟨238,(4),[1,2,5,6,13,14],[170],609⟩,⟨238,(4),[5,6],[174],609⟩,⟨238,(5),[1,2,5,6,13,14],[170],610⟩,⟨238,(5),[5,6],[174],610⟩,⟨238,(6),[1,2,5,6,13,14],[170],611⟩,⟨238,(6),[5,6],[174],298⟩,⟨238,(7),[1,2,5,6,13,14],[170],612⟩,⟨238,(7),[5,6],[174],298⟩,⟨238,(8),[1,2,5,6,13,14],[170],613⟩,⟨238,(8),[5,6],[174],613⟩,⟨238,(9),[1,2,5,6,13,14],[170],614⟩,⟨238,(9),[5,6],[174],614⟩,⟨238,(10),[1,2,5,6,13,14],[170],615⟩,⟨238,(10),[5,6],[174],299⟩,⟨238,(11),[1,2,5,6,13,14],[170],616⟩,⟨238,(11),[5,6],[174],299⟩,⟨238,(12),[1,2,5,6,13,14],[170],617⟩,⟨238,(12),[5,6],[174],617⟩,⟨238,(13),[1,2,5,6,13,14],[170],618⟩,⟨238,(13),[5,6],[174],618⟩,⟨238,(14),[1,2,5,6,13,14],[170],619⟩,⟨238,(14),[5,6],[174],300⟩,⟨238,(15),[1,2,5,6,13,14],[170],620⟩,⟨238,(15),[5,6],[174],300⟩,⟨242,(0),[1,2,5,6],[170],632⟩,⟨242,(0),[5,6],[174],632⟩,⟨242,(1),[1,2,5,6],[170],872⟩,⟨242,(1),[5,6],[174],872⟩,⟨242,(2),[1,2,5,6],[170],873⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3744
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3745
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3746
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3747
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3748
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3749
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3750
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3751
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3752
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3753
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3754
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3755
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3756
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3757
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3758
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3759
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3760
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3761
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3762
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3763
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3764
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3765
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3766
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3767
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3768
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3769
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3770
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3771
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3772
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3773
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3774
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3775
end Section14Records_6_3744_3776

#print axioms solution
