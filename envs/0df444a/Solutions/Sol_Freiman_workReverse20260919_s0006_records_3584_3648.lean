-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3584_3648
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:33:56.848527+00:00
-- url     : https://prove2.me/submissions/52e8bcac-71e2-46ae-9832-1047bd0d137c

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3584_3616
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3584_3616
private theorem valid3584 : RecordDataValid section14Catalog 6 (⟨231,(14),[5,6],[174],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3585 : RecordDataValid section14Catalog 6 (⟨231,(15),[1,2,5,6,13,14],[170],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3586 : RecordDataValid section14Catalog 6 (⟨231,(15),[5,6],[174],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3587 : RecordDataValid section14Catalog 6 (⟨231,(16),[1,2,5,6,13,14],[170],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3588 : RecordDataValid section14Catalog 6 (⟨231,(16),[5,6],[174],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3589 : RecordDataValid section14Catalog 6 (⟨231,(17),[1,2,5,6,13,14],[170],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3590 : RecordDataValid section14Catalog 6 (⟨231,(17),[5,6],[174],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3591 : RecordDataValid section14Catalog 6 (⟨231,(18),[1,2,5,6,13,14],[170],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3592 : RecordDataValid section14Catalog 6 (⟨231,(18),[5,6],[174],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3593 : RecordDataValid section14Catalog 6 (⟨231,(19),[1,2,5,6,13,14],[170],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3594 : RecordDataValid section14Catalog 6 (⟨231,(19),[5,6],[174],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3595 : RecordDataValid section14Catalog 6 (⟨232,(0),[1,2,5,6,13,14],[170],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3596 : RecordDataValid section14Catalog 6 (⟨232,(0),[5,6],[174],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3597 : RecordDataValid section14Catalog 6 (⟨232,(1),[1,2,5,6,13,14],[170],845⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3598 : RecordDataValid section14Catalog 6 (⟨232,(1),[5,6],[174],845⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3599 : RecordDataValid section14Catalog 6 (⟨232,(2),[1,2,5,6,13,14],[170],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3600 : RecordDataValid section14Catalog 6 (⟨232,(2),[5,6],[174],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3601 : RecordDataValid section14Catalog 6 (⟨232,(3),[1,2,5,6,13,14],[170],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3602 : RecordDataValid section14Catalog 6 (⟨232,(3),[5,6],[174],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3603 : RecordDataValid section14Catalog 6 (⟨232,(4),[1,5,6,13],[170],848⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨848,[1,4,5,6,8,9,10,11,12,13,16],849⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3604 : RecordDataValid section14Catalog 6 (⟨232,(4),[5,6],[174],1069⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1069,[3,5,6,7],1073⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3605 : RecordDataValid section14Catalog 6 (⟨232,(5),[1,2,5,6,13,14],[170],849⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3606 : RecordDataValid section14Catalog 6 (⟨232,(5),[5,6],[174],849⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3607 : RecordDataValid section14Catalog 6 (⟨232,(6),[1,2,5,6,13,14],[170],850⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3608 : RecordDataValid section14Catalog 6 (⟨232,(6),[5,6],[174],850⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3609 : RecordDataValid section14Catalog 6 (⟨232,(7),[1,2,5,6,13,14],[170],851⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3610 : RecordDataValid section14Catalog 6 (⟨232,(7),[5,6],[174],851⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3611 : RecordDataValid section14Catalog 6 (⟨232,(8),[1,2,5,6,13,14],[170],852⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3612 : RecordDataValid section14Catalog 6 (⟨232,(8),[5,6],[174],852⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3613 : RecordDataValid section14Catalog 6 (⟨232,(9),[1,2,5,6,13,14],[170],853⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨853,[1,2,3,5,6,7,10,11,13,14,15],854⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3614 : RecordDataValid section14Catalog 6 (⟨232,(9),[5,6],[174],1070⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1070,[3,5,6,7],1074⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3615 : RecordDataValid section14Catalog 6 (⟨232,(10),[1,2,5,6,13,14],[170],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3584_3616 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3584).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3584).take 32 = [⟨231,(14),[5,6],[174],838⟩,⟨231,(15),[1,2,5,6,13,14],[170],840⟩,⟨231,(15),[5,6],[174],840⟩,⟨231,(16),[1,2,5,6,13,14],[170],841⟩,⟨231,(16),[5,6],[174],841⟩,⟨231,(17),[1,2,5,6,13,14],[170],842⟩,⟨231,(17),[5,6],[174],842⟩,⟨231,(18),[1,2,5,6,13,14],[170],841⟩,⟨231,(18),[5,6],[174],841⟩,⟨231,(19),[1,2,5,6,13,14],[170],843⟩,⟨231,(19),[5,6],[174],843⟩,⟨232,(0),[1,2,5,6,13,14],[170],844⟩,⟨232,(0),[5,6],[174],844⟩,⟨232,(1),[1,2,5,6,13,14],[170],845⟩,⟨232,(1),[5,6],[174],845⟩,⟨232,(2),[1,2,5,6,13,14],[170],846⟩,⟨232,(2),[5,6],[174],846⟩,⟨232,(3),[1,2,5,6,13,14],[170],847⟩,⟨232,(3),[5,6],[174],847⟩,⟨232,(4),[1,5,6,13],[170],848⟩,⟨232,(4),[5,6],[174],1069⟩,⟨232,(5),[1,2,5,6,13,14],[170],849⟩,⟨232,(5),[5,6],[174],849⟩,⟨232,(6),[1,2,5,6,13,14],[170],850⟩,⟨232,(6),[5,6],[174],850⟩,⟨232,(7),[1,2,5,6,13,14],[170],851⟩,⟨232,(7),[5,6],[174],851⟩,⟨232,(8),[1,2,5,6,13,14],[170],852⟩,⟨232,(8),[5,6],[174],852⟩,⟨232,(9),[1,2,5,6,13,14],[170],853⟩,⟨232,(9),[5,6],[174],1070⟩,⟨232,(10),[1,2,5,6,13,14],[170],844⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3584
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3585
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3586
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3587
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3588
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3589
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3590
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3591
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3592
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3593
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3594
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3595
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3596
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3597
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3598
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3599
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3600
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3601
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3602
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3603
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3604
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3605
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3606
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3607
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3608
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3609
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3610
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3611
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3612
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3613
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3614
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3615
end Section14Records_6_3584_3616

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3584_3616


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3616_3648
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3616_3648
private theorem valid3616 : RecordDataValid section14Catalog 6 (⟨232,(10),[5,6],[174],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3617 : RecordDataValid section14Catalog 6 (⟨232,(11),[1,2,5,6,13,14],[170],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3618 : RecordDataValid section14Catalog 6 (⟨232,(11),[5,6],[174],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3619 : RecordDataValid section14Catalog 6 (⟨232,(12),[1,2,5,6,13,14],[170],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3620 : RecordDataValid section14Catalog 6 (⟨232,(12),[5,6],[174],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3621 : RecordDataValid section14Catalog 6 (⟨232,(13),[1,2,5,6,13,14],[170],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3622 : RecordDataValid section14Catalog 6 (⟨232,(13),[5,6],[174],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3623 : RecordDataValid section14Catalog 6 (⟨232,(14),[1,2,5,6,13,14],[170],855⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨855,[1,2,3,5,6,7,10,11,13,14,15],856⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3624 : RecordDataValid section14Catalog 6 (⟨232,(14),[5,6],[174],1069⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1069,[3,5,6,7],1073⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3625 : RecordDataValid section14Catalog 6 (⟨232,(15),[1,2,5,6,13,14],[170],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3626 : RecordDataValid section14Catalog 6 (⟨232,(15),[5,6],[174],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3627 : RecordDataValid section14Catalog 6 (⟨232,(16),[1,2,5,6,13,14],[170],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3628 : RecordDataValid section14Catalog 6 (⟨232,(16),[5,6],[174],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3629 : RecordDataValid section14Catalog 6 (⟨232,(17),[1,2,5,6,13,14],[170],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3630 : RecordDataValid section14Catalog 6 (⟨232,(17),[5,6],[174],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3631 : RecordDataValid section14Catalog 6 (⟨232,(18),[1,2,5,6,13,14],[170],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3632 : RecordDataValid section14Catalog 6 (⟨232,(18),[5,6],[174],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3633 : RecordDataValid section14Catalog 6 (⟨232,(19),[1,2,5,6,13,14],[170],860⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨860,[1,2,3,5,6,7,10,11,13,14,15],861⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3634 : RecordDataValid section14Catalog 6 (⟨232,(19),[5,6],[174],1071⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1071,[3,5,6,7],1075⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3635 : RecordDataValid section14Catalog 6 (⟨234,(0),[1,2,5,6,13,14],[170],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3636 : RecordDataValid section14Catalog 6 (⟨234,(0),[5,6],[174],1072⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1072,[3,5,6,7],1076⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3637 : RecordDataValid section14Catalog 6 (⟨234,(1),[1,2,5,6,13,14],[170],569⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨569,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],570⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3638 : RecordDataValid section14Catalog 6 (⟨234,(1),[5,6],[174],1073⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1073,[3,5,6,7],1077⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3639 : RecordDataValid section14Catalog 6 (⟨234,(2),[1,2,5,6,13,14],[170],570⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨570,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],571⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3640 : RecordDataValid section14Catalog 6 (⟨234,(2),[5,6],[174],1072⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1072,[3,5,6,7],1076⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3641 : RecordDataValid section14Catalog 6 (⟨234,(3),[1,2,5,6,13,14],[170],571⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨571,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],572⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3642 : RecordDataValid section14Catalog 6 (⟨234,(3),[5,6],[174],1074⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1074,[3,5,6,7],1078⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3643 : RecordDataValid section14Catalog 6 (⟨234,(4),[1,2,5,6,13,14],[170],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3644 : RecordDataValid section14Catalog 6 (⟨234,(4),[5,6],[174],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3645 : RecordDataValid section14Catalog 6 (⟨234,(5),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3646 : RecordDataValid section14Catalog 6 (⟨234,(5),[5,6],[174],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3647 : RecordDataValid section14Catalog 6 (⟨234,(6),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3616_3648 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3616).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3616).take 32 = [⟨232,(10),[5,6],[174],844⟩,⟨232,(11),[1,2,5,6,13,14],[170],854⟩,⟨232,(11),[5,6],[174],854⟩,⟨232,(12),[1,2,5,6,13,14],[170],846⟩,⟨232,(12),[5,6],[174],846⟩,⟨232,(13),[1,2,5,6,13,14],[170],847⟩,⟨232,(13),[5,6],[174],847⟩,⟨232,(14),[1,2,5,6,13,14],[170],855⟩,⟨232,(14),[5,6],[174],1069⟩,⟨232,(15),[1,2,5,6,13,14],[170],856⟩,⟨232,(15),[5,6],[174],856⟩,⟨232,(16),[1,2,5,6,13,14],[170],857⟩,⟨232,(16),[5,6],[174],857⟩,⟨232,(17),[1,2,5,6,13,14],[170],858⟩,⟨232,(17),[5,6],[174],858⟩,⟨232,(18),[1,2,5,6,13,14],[170],859⟩,⟨232,(18),[5,6],[174],859⟩,⟨232,(19),[1,2,5,6,13,14],[170],860⟩,⟨232,(19),[5,6],[174],1071⟩,⟨234,(0),[1,2,5,6,13,14],[170],568⟩,⟨234,(0),[5,6],[174],1072⟩,⟨234,(1),[1,2,5,6,13,14],[170],569⟩,⟨234,(1),[5,6],[174],1073⟩,⟨234,(2),[1,2,5,6,13,14],[170],570⟩,⟨234,(2),[5,6],[174],1072⟩,⟨234,(3),[1,2,5,6,13,14],[170],571⟩,⟨234,(3),[5,6],[174],1074⟩,⟨234,(4),[1,2,5,6,13,14],[170],572⟩,⟨234,(4),[5,6],[174],1075⟩,⟨234,(5),[1,2,5,6,13,14],[170],573⟩,⟨234,(5),[5,6],[174],1075⟩,⟨234,(6),[1,2,5,6,13,14],[170],573⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3616
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3617
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3618
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3619
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3620
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3621
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3622
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3623
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3624
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3625
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3626
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3627
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3628
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3629
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3630
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3631
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3632
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3633
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3634
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3635
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3636
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3637
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3638
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3639
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3640
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3641
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3642
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3643
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3644
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3645
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3646
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3647
end Section14Records_6_3616_3648

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3616_3648

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3584).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 3584 3616 3648 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3584_3616 hnum) (Freiman.workReverse20260919_s0006_records_3616_3648 hnum))

#print axioms solution
