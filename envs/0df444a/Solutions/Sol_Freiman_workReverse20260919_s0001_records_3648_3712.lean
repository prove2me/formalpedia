-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3648_3712
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:34:39.763206+00:00
-- url     : https://prove2.me/submissions/82775ef0-623e-4a39-b176-a9a0a2ba67b2

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3648_3680
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3648_3680
private theorem valid3648 : RecordDataValid section14Catalog 1 (⟨230,(19),[1,2,5,6,13,14],[170],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3649 : RecordDataValid section14Catalog 1 (⟨230,(20),[1,2,5,6,13,14],[170],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3650 : RecordDataValid section14Catalog 1 (⟨230,(21),[1,2,5,6,13,14],[170],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3651 : RecordDataValid section14Catalog 1 (⟨230,(22),[1,2,5,6,13,14],[170],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3652 : RecordDataValid section14Catalog 1 (⟨230,(23),[1,2,5,6,13,14],[170],829⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3653 : RecordDataValid section14Catalog 1 (⟨230,(24),[1,2,5,6,13,14],[170],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3654 : RecordDataValid section14Catalog 1 (⟨231,(0),[1,2,5,6,13,14],[170],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3655 : RecordDataValid section14Catalog 1 (⟨231,(1),[1,2,5,6,13,14],[170],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3656 : RecordDataValid section14Catalog 1 (⟨231,(2),[1,2,5,6,13,14],[170],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3657 : RecordDataValid section14Catalog 1 (⟨231,(3),[1,2,5,6,13,14],[170],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3658 : RecordDataValid section14Catalog 1 (⟨231,(4),[1,2,5,6,13,14],[170],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3659 : RecordDataValid section14Catalog 1 (⟨231,(5),[1,2,5,6,13,14],[170],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3660 : RecordDataValid section14Catalog 1 (⟨231,(6),[1,2,5,6,13,14],[170],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3661 : RecordDataValid section14Catalog 1 (⟨231,(7),[1,2,5,6,13,14],[170],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3662 : RecordDataValid section14Catalog 1 (⟨231,(8),[1,2,5,6,13,14],[170],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3663 : RecordDataValid section14Catalog 1 (⟨231,(9),[1,2,5,6,13,14],[170],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3664 : RecordDataValid section14Catalog 1 (⟨231,(10),[1,2,5,6,13,14],[170],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3665 : RecordDataValid section14Catalog 1 (⟨231,(11),[1,2,5,6,13,14],[170],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3666 : RecordDataValid section14Catalog 1 (⟨231,(12),[1,2,5,6,13,14],[170],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3667 : RecordDataValid section14Catalog 1 (⟨231,(13),[1,2,5,6,13,14],[170],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3668 : RecordDataValid section14Catalog 1 (⟨231,(14),[1,2,5,6,13,14],[170],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3669 : RecordDataValid section14Catalog 1 (⟨231,(15),[1,2,5,6,13,14],[170],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3670 : RecordDataValid section14Catalog 1 (⟨231,(16),[1,2,5,6,13,14],[170],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3671 : RecordDataValid section14Catalog 1 (⟨231,(17),[1,2,5,6,13,14],[170],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3672 : RecordDataValid section14Catalog 1 (⟨231,(18),[1,2,5,6,13,14],[170],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3673 : RecordDataValid section14Catalog 1 (⟨231,(19),[1,2,5,6,13,14],[170],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3674 : RecordDataValid section14Catalog 1 (⟨232,(0),[1,2,5,6,13,14],[170],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3675 : RecordDataValid section14Catalog 1 (⟨232,(1),[1,2,5,6,13,14],[170],845⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3676 : RecordDataValid section14Catalog 1 (⟨232,(2),[1,2,5,6,13,14],[170],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3677 : RecordDataValid section14Catalog 1 (⟨232,(3),[1,2,5,6,13,14],[170],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3678 : RecordDataValid section14Catalog 1 (⟨232,(4),[1,5,6,13],[170],848⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨848,[1,4,5,6,8,9,10,11,12,13,16],849⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3679 : RecordDataValid section14Catalog 1 (⟨232,(5),[1,2,5,6,13,14],[170],849⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3648_3680 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3648).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3648).take 32 = [⟨230,(19),[1,2,5,6,13,14],[170],824⟩,⟨230,(20),[1,2,5,6,13,14],[170],826⟩,⟨230,(21),[1,2,5,6,13,14],[170],827⟩,⟨230,(22),[1,2,5,6,13,14],[170],828⟩,⟨230,(23),[1,2,5,6,13,14],[170],829⟩,⟨230,(24),[1,2,5,6,13,14],[170],828⟩,⟨231,(0),[1,2,5,6,13,14],[170],830⟩,⟨231,(1),[1,2,5,6,13,14],[170],831⟩,⟨231,(2),[1,2,5,6,13,14],[170],832⟩,⟨231,(3),[1,2,5,6,13,14],[170],833⟩,⟨231,(4),[1,2,5,6,13,14],[170],830⟩,⟨231,(5),[1,2,5,6,13,14],[170],831⟩,⟨231,(6),[1,2,5,6,13,14],[170],832⟩,⟨231,(7),[1,2,5,6,13,14],[170],833⟩,⟨231,(8),[1,2,5,6,13,14],[170],834⟩,⟨231,(9),[1,2,5,6,13,14],[170],835⟩,⟨231,(10),[1,2,5,6,13,14],[170],836⟩,⟨231,(11),[1,2,5,6,13,14],[170],837⟩,⟨231,(12),[1,2,5,6,13,14],[170],838⟩,⟨231,(13),[1,2,5,6,13,14],[170],839⟩,⟨231,(14),[1,2,5,6,13,14],[170],838⟩,⟨231,(15),[1,2,5,6,13,14],[170],840⟩,⟨231,(16),[1,2,5,6,13,14],[170],841⟩,⟨231,(17),[1,2,5,6,13,14],[170],842⟩,⟨231,(18),[1,2,5,6,13,14],[170],841⟩,⟨231,(19),[1,2,5,6,13,14],[170],843⟩,⟨232,(0),[1,2,5,6,13,14],[170],844⟩,⟨232,(1),[1,2,5,6,13,14],[170],845⟩,⟨232,(2),[1,2,5,6,13,14],[170],846⟩,⟨232,(3),[1,2,5,6,13,14],[170],847⟩,⟨232,(4),[1,5,6,13],[170],848⟩,⟨232,(5),[1,2,5,6,13,14],[170],849⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3648
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3649
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3650
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3651
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3652
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3653
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3654
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3655
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3656
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3657
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3658
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3659
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3660
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3661
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3662
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3663
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3664
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3665
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3666
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3667
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3668
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3669
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3670
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3671
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3672
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3673
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3674
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3675
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3676
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3677
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3678
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3679
end Section14Records_1_3648_3680

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3648_3680


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3680_3712
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3680_3712
private theorem valid3680 : RecordDataValid section14Catalog 1 (⟨232,(6),[1,2,5,6,13,14],[170],850⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3681 : RecordDataValid section14Catalog 1 (⟨232,(7),[1,2,5,6,13,14],[170],851⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3682 : RecordDataValid section14Catalog 1 (⟨232,(8),[1,2,5,6,13,14],[170],852⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3683 : RecordDataValid section14Catalog 1 (⟨232,(9),[1,2,5,6,13,14],[170],853⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨853,[1,2,3,5,6,7,10,11,13,14,15],854⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3684 : RecordDataValid section14Catalog 1 (⟨232,(10),[1,2,5,6,13,14],[170],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3685 : RecordDataValid section14Catalog 1 (⟨232,(11),[1,2,5,6,13,14],[170],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3686 : RecordDataValid section14Catalog 1 (⟨232,(12),[1,2,5,6,13,14],[170],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3687 : RecordDataValid section14Catalog 1 (⟨232,(13),[1,2,5,6,13,14],[170],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3688 : RecordDataValid section14Catalog 1 (⟨232,(14),[1,2,5,6,13,14],[170],855⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨855,[1,2,3,5,6,7,10,11,13,14,15],856⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3689 : RecordDataValid section14Catalog 1 (⟨232,(15),[1,2,5,6,13,14],[170],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3690 : RecordDataValid section14Catalog 1 (⟨232,(16),[1,2,5,6,13,14],[170],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3691 : RecordDataValid section14Catalog 1 (⟨232,(17),[1,2,5,6,13,14],[170],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3692 : RecordDataValid section14Catalog 1 (⟨232,(18),[1,2,5,6,13,14],[170],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3693 : RecordDataValid section14Catalog 1 (⟨232,(19),[1,2,5,6,13,14],[170],860⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨860,[1,2,3,5,6,7,10,11,13,14,15],861⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3694 : RecordDataValid section14Catalog 1 (⟨234,(0),[1,2,5,6,13,14],[170],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3695 : RecordDataValid section14Catalog 1 (⟨234,(1),[1,2,5,6,13,14],[170],569⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨569,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],570⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3696 : RecordDataValid section14Catalog 1 (⟨234,(2),[1,2,5,6,13,14],[170],570⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨570,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],571⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3697 : RecordDataValid section14Catalog 1 (⟨234,(3),[1,2,5,6,13,14],[170],571⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨571,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],572⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3698 : RecordDataValid section14Catalog 1 (⟨234,(4),[1,2,5,6,13,14],[170],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3699 : RecordDataValid section14Catalog 1 (⟨234,(5),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3700 : RecordDataValid section14Catalog 1 (⟨234,(6),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3701 : RecordDataValid section14Catalog 1 (⟨234,(7),[1,2,5,6,13,14],[170],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3702 : RecordDataValid section14Catalog 1 (⟨234,(8),[1,2,5,6,13,14],[170],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3703 : RecordDataValid section14Catalog 1 (⟨234,(9),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3704 : RecordDataValid section14Catalog 1 (⟨234,(10),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3705 : RecordDataValid section14Catalog 1 (⟨234,(11),[1,2,5,6,13,14],[170],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3706 : RecordDataValid section14Catalog 1 (⟨234,(12),[1,2,5,6,13,14],[170],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3707 : RecordDataValid section14Catalog 1 (⟨234,(13),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3708 : RecordDataValid section14Catalog 1 (⟨234,(14),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3709 : RecordDataValid section14Catalog 1 (⟨234,(15),[1,2,5,6,13,14],[170],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3710 : RecordDataValid section14Catalog 1 (⟨235,(0),[1,2,5,6,13,14],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3711 : RecordDataValid section14Catalog 1 (⟨235,(1),[1,2,5,6,13,14],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3680_3712 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3680).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3680).take 32 = [⟨232,(6),[1,2,5,6,13,14],[170],850⟩,⟨232,(7),[1,2,5,6,13,14],[170],851⟩,⟨232,(8),[1,2,5,6,13,14],[170],852⟩,⟨232,(9),[1,2,5,6,13,14],[170],853⟩,⟨232,(10),[1,2,5,6,13,14],[170],844⟩,⟨232,(11),[1,2,5,6,13,14],[170],854⟩,⟨232,(12),[1,2,5,6,13,14],[170],846⟩,⟨232,(13),[1,2,5,6,13,14],[170],847⟩,⟨232,(14),[1,2,5,6,13,14],[170],855⟩,⟨232,(15),[1,2,5,6,13,14],[170],856⟩,⟨232,(16),[1,2,5,6,13,14],[170],857⟩,⟨232,(17),[1,2,5,6,13,14],[170],858⟩,⟨232,(18),[1,2,5,6,13,14],[170],859⟩,⟨232,(19),[1,2,5,6,13,14],[170],860⟩,⟨234,(0),[1,2,5,6,13,14],[170],568⟩,⟨234,(1),[1,2,5,6,13,14],[170],569⟩,⟨234,(2),[1,2,5,6,13,14],[170],570⟩,⟨234,(3),[1,2,5,6,13,14],[170],571⟩,⟨234,(4),[1,2,5,6,13,14],[170],572⟩,⟨234,(5),[1,2,5,6,13,14],[170],573⟩,⟨234,(6),[1,2,5,6,13,14],[170],573⟩,⟨234,(7),[1,2,5,6,13,14],[170],573⟩,⟨234,(8),[1,2,5,6,13,14],[170],574⟩,⟨234,(9),[1,2,5,6,13,14],[170],575⟩,⟨234,(10),[1,2,5,6,13,14],[170],575⟩,⟨234,(11),[1,2,5,6,13,14],[170],575⟩,⟨234,(12),[1,2,5,6,13,14],[170],576⟩,⟨234,(13),[1,2,5,6,13,14],[170],577⟩,⟨234,(14),[1,2,5,6,13,14],[170],577⟩,⟨234,(15),[1,2,5,6,13,14],[170],577⟩,⟨235,(0),[1,2,5,6,13,14],[170],578⟩,⟨235,(1),[1,2,5,6,13,14],[170],579⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3680
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3681
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3682
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3683
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3684
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3685
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3686
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3687
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3688
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3689
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3690
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3691
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3692
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3693
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3694
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3695
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3696
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3697
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3698
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3699
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3700
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3701
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3702
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3703
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3704
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3705
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3706
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3707
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3708
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3709
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3710
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3711
end Section14Records_1_3680_3712

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3680_3712

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3648).take 64, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 3648 3680 3712 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_3648_3680 hnum) (Freiman.workReverse20260919_s0001_records_3680_3712 hnum))

#print axioms solution
