-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3456_3520
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:31:01.353008+00:00
-- url     : https://prove2.me/submissions/5ae51c31-7c17-4492-99bb-c188227fc52e

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3456_3488
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3456_3488
private theorem valid3456 : RecordDataValid section14Catalog 6 (⟨228,(0),[5,6],[174],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3457 : RecordDataValid section14Catalog 6 (⟨228,(1),[1,2,5,6,13,14],[170],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3458 : RecordDataValid section14Catalog 6 (⟨228,(1),[5,6],[174],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3459 : RecordDataValid section14Catalog 6 (⟨228,(2),[1,5,6,13],[170],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3460 : RecordDataValid section14Catalog 6 (⟨228,(2),[5,6],[174],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3461 : RecordDataValid section14Catalog 6 (⟨228,(3),[1,2,5,6,13,14],[170],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3462 : RecordDataValid section14Catalog 6 (⟨228,(3),[5,6],[174],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3463 : RecordDataValid section14Catalog 6 (⟨228,(4),[1,2,5,6,13,14],[170],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3464 : RecordDataValid section14Catalog 6 (⟨228,(4),[5,6],[174],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3465 : RecordDataValid section14Catalog 6 (⟨228,(5),[1,2,5,6,13,14],[170],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3466 : RecordDataValid section14Catalog 6 (⟨228,(5),[5,6],[174],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3467 : RecordDataValid section14Catalog 6 (⟨228,(6),[1,2,5,6,13,14],[170],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3468 : RecordDataValid section14Catalog 6 (⟨228,(6),[5,6],[174],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3469 : RecordDataValid section14Catalog 6 (⟨228,(7),[1,2,5,6,13,14],[170],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3470 : RecordDataValid section14Catalog 6 (⟨228,(7),[5,6],[174],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3471 : RecordDataValid section14Catalog 6 (⟨228,(8),[1,2,5,6,13,14],[170],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3472 : RecordDataValid section14Catalog 6 (⟨228,(8),[5,6],[174],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3473 : RecordDataValid section14Catalog 6 (⟨228,(9),[1,2,5,6,13,14],[170],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3474 : RecordDataValid section14Catalog 6 (⟨228,(9),[5,6],[174],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3475 : RecordDataValid section14Catalog 6 (⟨228,(10),[1,2,5,6,13,14],[170],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3476 : RecordDataValid section14Catalog 6 (⟨228,(10),[5,6],[174],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3477 : RecordDataValid section14Catalog 6 (⟨228,(11),[1,2,5,6,13,14],[170],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3478 : RecordDataValid section14Catalog 6 (⟨228,(11),[5,6],[174],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3479 : RecordDataValid section14Catalog 6 (⟨228,(12),[1,2,5,6,13,14],[170],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3480 : RecordDataValid section14Catalog 6 (⟨228,(12),[5,6],[174],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3481 : RecordDataValid section14Catalog 6 (⟨228,(13),[1,2,5,6,13,14],[170],801⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3482 : RecordDataValid section14Catalog 6 (⟨228,(13),[5,6],[174],801⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3483 : RecordDataValid section14Catalog 6 (⟨228,(14),[1,2,5,6,13,14],[170],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3484 : RecordDataValid section14Catalog 6 (⟨228,(14),[5,6],[174],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3485 : RecordDataValid section14Catalog 6 (⟨228,(15),[1,2,5,6,13,14],[170],802⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3486 : RecordDataValid section14Catalog 6 (⟨228,(15),[5,6],[174],802⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3487 : RecordDataValid section14Catalog 6 (⟨228,(16),[1,2,5,6,13,14],[170],803⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3456_3488 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3456).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3456).take 32 = [⟨228,(0),[5,6],[174],789⟩,⟨228,(1),[1,2,5,6,13,14],[170],790⟩,⟨228,(1),[5,6],[174],790⟩,⟨228,(2),[1,5,6,13],[170],791⟩,⟨228,(2),[5,6],[174],791⟩,⟨228,(3),[1,2,5,6,13,14],[170],792⟩,⟨228,(3),[5,6],[174],792⟩,⟨228,(4),[1,2,5,6,13,14],[170],793⟩,⟨228,(4),[5,6],[174],793⟩,⟨228,(5),[1,2,5,6,13,14],[170],794⟩,⟨228,(5),[5,6],[174],794⟩,⟨228,(6),[1,2,5,6,13,14],[170],795⟩,⟨228,(6),[5,6],[174],795⟩,⟨228,(7),[1,2,5,6,13,14],[170],796⟩,⟨228,(7),[5,6],[174],796⟩,⟨228,(8),[1,2,5,6,13,14],[170],797⟩,⟨228,(8),[5,6],[174],797⟩,⟨228,(9),[1,2,5,6,13,14],[170],796⟩,⟨228,(9),[5,6],[174],796⟩,⟨228,(10),[1,2,5,6,13,14],[170],798⟩,⟨228,(10),[5,6],[174],798⟩,⟨228,(11),[1,2,5,6,13,14],[170],799⟩,⟨228,(11),[5,6],[174],799⟩,⟨228,(12),[1,2,5,6,13,14],[170],800⟩,⟨228,(12),[5,6],[174],800⟩,⟨228,(13),[1,2,5,6,13,14],[170],801⟩,⟨228,(13),[5,6],[174],801⟩,⟨228,(14),[1,2,5,6,13,14],[170],800⟩,⟨228,(14),[5,6],[174],800⟩,⟨228,(15),[1,2,5,6,13,14],[170],802⟩,⟨228,(15),[5,6],[174],802⟩,⟨228,(16),[1,2,5,6,13,14],[170],803⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3456
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3457
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3458
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3459
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3460
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3461
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3462
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3463
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3464
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3465
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3466
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3467
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3468
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3469
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3470
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3471
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3472
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3473
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3474
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3475
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3476
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3477
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3478
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3479
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3480
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3481
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3482
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3483
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3484
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3485
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3486
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3487
end Section14Records_6_3456_3488

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3456_3488


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3488_3520
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3488_3520
private theorem valid3488 : RecordDataValid section14Catalog 6 (⟨228,(16),[5,6],[174],803⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3489 : RecordDataValid section14Catalog 6 (⟨228,(17),[1,2,5,6,13,14],[170],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3490 : RecordDataValid section14Catalog 6 (⟨228,(17),[5,6],[174],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3491 : RecordDataValid section14Catalog 6 (⟨228,(18),[1,2,5,6,13,14],[170],805⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3492 : RecordDataValid section14Catalog 6 (⟨228,(18),[5,6],[174],805⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3493 : RecordDataValid section14Catalog 6 (⟨228,(19),[1,2,5,6,13,14],[170],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3494 : RecordDataValid section14Catalog 6 (⟨228,(19),[5,6],[174],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3495 : RecordDataValid section14Catalog 6 (⟨228,(20),[1,2,5,6,13,14],[170],806⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3496 : RecordDataValid section14Catalog 6 (⟨228,(20),[5,6],[174],806⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3497 : RecordDataValid section14Catalog 6 (⟨228,(21),[1,2,5,6,13,14],[170],807⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3498 : RecordDataValid section14Catalog 6 (⟨228,(21),[5,6],[174],807⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3499 : RecordDataValid section14Catalog 6 (⟨228,(22),[1,2,5,6,13,14],[170],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3500 : RecordDataValid section14Catalog 6 (⟨228,(22),[5,6],[174],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3501 : RecordDataValid section14Catalog 6 (⟨228,(23),[1,2,5,6,13,14],[170],809⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3502 : RecordDataValid section14Catalog 6 (⟨228,(23),[5,6],[174],809⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3503 : RecordDataValid section14Catalog 6 (⟨228,(24),[1,2,5,6,13,14],[170],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3504 : RecordDataValid section14Catalog 6 (⟨228,(24),[5,6],[174],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3505 : RecordDataValid section14Catalog 6 (⟨230,(0),[1,2,5,6,13,14],[170],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3506 : RecordDataValid section14Catalog 6 (⟨230,(0),[5,6],[174],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3507 : RecordDataValid section14Catalog 6 (⟨230,(1),[1,2,5,6,13,14],[170],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3508 : RecordDataValid section14Catalog 6 (⟨230,(1),[5,6],[174],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3509 : RecordDataValid section14Catalog 6 (⟨230,(2),[1,2,5,6,13,14],[170],812⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3510 : RecordDataValid section14Catalog 6 (⟨230,(2),[5,6],[174],812⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3511 : RecordDataValid section14Catalog 6 (⟨230,(3),[1,2,5,6,13,14],[170],813⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3512 : RecordDataValid section14Catalog 6 (⟨230,(3),[5,6],[174],813⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3513 : RecordDataValid section14Catalog 6 (⟨230,(4),[1,2,5,6,13,14],[170],814⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨814,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],815⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3514 : RecordDataValid section14Catalog 6 (⟨230,(4),[5,6],[174],814⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨814,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],815⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3515 : RecordDataValid section14Catalog 6 (⟨230,(5),[1,2,5,6,13,14],[170],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3516 : RecordDataValid section14Catalog 6 (⟨230,(5),[5,6],[174],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3517 : RecordDataValid section14Catalog 6 (⟨230,(6),[1,2,5,6,13,14],[170],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3518 : RecordDataValid section14Catalog 6 (⟨230,(6),[5,6],[174],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3519 : RecordDataValid section14Catalog 6 (⟨230,(7),[1,5,6,13],[170],815⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨815,[1,4,5,6,8,9,10,12,13,16],816⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3488_3520 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3488).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3488).take 32 = [⟨228,(16),[5,6],[174],803⟩,⟨228,(17),[1,2,5,6,13,14],[170],804⟩,⟨228,(17),[5,6],[174],804⟩,⟨228,(18),[1,2,5,6,13,14],[170],805⟩,⟨228,(18),[5,6],[174],805⟩,⟨228,(19),[1,2,5,6,13,14],[170],804⟩,⟨228,(19),[5,6],[174],804⟩,⟨228,(20),[1,2,5,6,13,14],[170],806⟩,⟨228,(20),[5,6],[174],806⟩,⟨228,(21),[1,2,5,6,13,14],[170],807⟩,⟨228,(21),[5,6],[174],807⟩,⟨228,(22),[1,2,5,6,13,14],[170],808⟩,⟨228,(22),[5,6],[174],808⟩,⟨228,(23),[1,2,5,6,13,14],[170],809⟩,⟨228,(23),[5,6],[174],809⟩,⟨228,(24),[1,2,5,6,13,14],[170],808⟩,⟨228,(24),[5,6],[174],808⟩,⟨230,(0),[1,2,5,6,13,14],[170],810⟩,⟨230,(0),[5,6],[174],810⟩,⟨230,(1),[1,2,5,6,13,14],[170],811⟩,⟨230,(1),[5,6],[174],811⟩,⟨230,(2),[1,2,5,6,13,14],[170],812⟩,⟨230,(2),[5,6],[174],812⟩,⟨230,(3),[1,2,5,6,13,14],[170],813⟩,⟨230,(3),[5,6],[174],813⟩,⟨230,(4),[1,2,5,6,13,14],[170],814⟩,⟨230,(4),[5,6],[174],814⟩,⟨230,(5),[1,2,5,6,13,14],[170],810⟩,⟨230,(5),[5,6],[174],810⟩,⟨230,(6),[1,2,5,6,13,14],[170],811⟩,⟨230,(6),[5,6],[174],811⟩,⟨230,(7),[1,5,6,13],[170],815⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3488
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3489
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3490
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3491
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3492
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3493
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3494
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3495
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3496
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3497
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3498
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3499
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3500
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3501
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3502
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3503
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3504
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3505
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3506
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3507
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3508
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3509
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3510
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3511
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3512
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3513
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3514
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3515
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3516
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3517
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3518
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3519
end Section14Records_6_3488_3520

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3488_3520

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3456).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 3456 3488 3520 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3456_3488 hnum) (Freiman.workReverse20260919_s0006_records_3488_3520 hnum))

#print axioms solution
