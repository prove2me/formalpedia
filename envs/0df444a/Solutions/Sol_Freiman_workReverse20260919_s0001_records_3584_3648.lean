-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3584_3648
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:33:46.174986+00:00
-- url     : https://prove2.me/submissions/c62f6edb-03ac-4c06-88af-720832d08a4b

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3584_3616
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3584_3616
private theorem valid3584 : RecordDataValid section14Catalog 1 (⟨227,(5),[1,2,5,6,13,14],[170],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3585 : RecordDataValid section14Catalog 1 (⟨227,(6),[1,2,5,6,13,14],[170],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3586 : RecordDataValid section14Catalog 1 (⟨227,(7),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3587 : RecordDataValid section14Catalog 1 (⟨227,(8),[1,2,5,6,13,14],[170],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3588 : RecordDataValid section14Catalog 1 (⟨227,(9),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3589 : RecordDataValid section14Catalog 1 (⟨227,(10),[1,2,5,6,13,14],[170],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3590 : RecordDataValid section14Catalog 1 (⟨227,(11),[1,2,5,6,13,14],[170],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3591 : RecordDataValid section14Catalog 1 (⟨227,(12),[1,2,5,6,13,14],[170],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3592 : RecordDataValid section14Catalog 1 (⟨227,(13),[1,2,5,6,13,14],[170],780⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3593 : RecordDataValid section14Catalog 1 (⟨227,(14),[1,2,5,6,13,14],[170],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3594 : RecordDataValid section14Catalog 1 (⟨227,(15),[1,2,5,6,13,14],[170],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3595 : RecordDataValid section14Catalog 1 (⟨227,(16),[1,2,5,6,13,14],[170],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3596 : RecordDataValid section14Catalog 1 (⟨227,(17),[1,2,5,6,13,14],[170],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3597 : RecordDataValid section14Catalog 1 (⟨227,(18),[1,2,5,6,13,14],[170],784⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3598 : RecordDataValid section14Catalog 1 (⟨227,(19),[1,2,5,6,13,14],[170],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3599 : RecordDataValid section14Catalog 1 (⟨227,(20),[1,2,5,6,13,14],[170],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3600 : RecordDataValid section14Catalog 1 (⟨227,(21),[1,2,5,6,13,14],[170],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3601 : RecordDataValid section14Catalog 1 (⟨227,(22),[1,2,5,6,13,14],[170],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3602 : RecordDataValid section14Catalog 1 (⟨227,(23),[1,2,5,6,13,14],[170],788⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3603 : RecordDataValid section14Catalog 1 (⟨227,(24),[1,2,5,6,13,14],[170],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3604 : RecordDataValid section14Catalog 1 (⟨228,(0),[1,2,5,6,13,14],[170],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3605 : RecordDataValid section14Catalog 1 (⟨228,(1),[1,2,5,6,13,14],[170],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3606 : RecordDataValid section14Catalog 1 (⟨228,(2),[1,5,6,13],[170],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3607 : RecordDataValid section14Catalog 1 (⟨228,(3),[1,2,5,6,13,14],[170],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3608 : RecordDataValid section14Catalog 1 (⟨228,(4),[1,2,5,6,13,14],[170],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3609 : RecordDataValid section14Catalog 1 (⟨228,(5),[1,2,5,6,13,14],[170],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3610 : RecordDataValid section14Catalog 1 (⟨228,(6),[1,2,5,6,13,14],[170],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3611 : RecordDataValid section14Catalog 1 (⟨228,(7),[1,2,5,6,13,14],[170],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3612 : RecordDataValid section14Catalog 1 (⟨228,(8),[1,2,5,6,13,14],[170],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3613 : RecordDataValid section14Catalog 1 (⟨228,(9),[1,2,5,6,13,14],[170],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3614 : RecordDataValid section14Catalog 1 (⟨228,(10),[1,2,5,6,13,14],[170],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3615 : RecordDataValid section14Catalog 1 (⟨228,(11),[1,2,5,6,13,14],[170],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3584_3616 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3584).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3584).take 32 = [⟨227,(5),[1,2,5,6,13,14],[170],773⟩,⟨227,(6),[1,2,5,6,13,14],[170],774⟩,⟨227,(7),[1,2,5,6,13,14],[170],775⟩,⟨227,(8),[1,2,5,6,13,14],[170],776⟩,⟨227,(9),[1,2,5,6,13,14],[170],775⟩,⟨227,(10),[1,2,5,6,13,14],[170],777⟩,⟨227,(11),[1,2,5,6,13,14],[170],778⟩,⟨227,(12),[1,2,5,6,13,14],[170],779⟩,⟨227,(13),[1,2,5,6,13,14],[170],780⟩,⟨227,(14),[1,2,5,6,13,14],[170],779⟩,⟨227,(15),[1,2,5,6,13,14],[170],781⟩,⟨227,(16),[1,2,5,6,13,14],[170],782⟩,⟨227,(17),[1,2,5,6,13,14],[170],783⟩,⟨227,(18),[1,2,5,6,13,14],[170],784⟩,⟨227,(19),[1,2,5,6,13,14],[170],783⟩,⟨227,(20),[1,2,5,6,13,14],[170],785⟩,⟨227,(21),[1,2,5,6,13,14],[170],786⟩,⟨227,(22),[1,2,5,6,13,14],[170],787⟩,⟨227,(23),[1,2,5,6,13,14],[170],788⟩,⟨227,(24),[1,2,5,6,13,14],[170],787⟩,⟨228,(0),[1,2,5,6,13,14],[170],789⟩,⟨228,(1),[1,2,5,6,13,14],[170],790⟩,⟨228,(2),[1,5,6,13],[170],791⟩,⟨228,(3),[1,2,5,6,13,14],[170],792⟩,⟨228,(4),[1,2,5,6,13,14],[170],793⟩,⟨228,(5),[1,2,5,6,13,14],[170],794⟩,⟨228,(6),[1,2,5,6,13,14],[170],795⟩,⟨228,(7),[1,2,5,6,13,14],[170],796⟩,⟨228,(8),[1,2,5,6,13,14],[170],797⟩,⟨228,(9),[1,2,5,6,13,14],[170],796⟩,⟨228,(10),[1,2,5,6,13,14],[170],798⟩,⟨228,(11),[1,2,5,6,13,14],[170],799⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3584
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3585
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3586
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3587
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3588
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3589
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3590
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3591
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3592
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3593
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3594
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3595
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3596
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3597
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3598
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3599
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3600
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3601
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3602
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3603
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3604
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3605
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3606
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3607
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3608
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3609
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3610
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3611
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3612
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3613
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3614
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3615
end Section14Records_1_3584_3616

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3584_3616


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3616_3648
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3616_3648
private theorem valid3616 : RecordDataValid section14Catalog 1 (⟨228,(12),[1,2,5,6,13,14],[170],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3617 : RecordDataValid section14Catalog 1 (⟨228,(13),[1,2,5,6,13,14],[170],801⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3618 : RecordDataValid section14Catalog 1 (⟨228,(14),[1,2,5,6,13,14],[170],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3619 : RecordDataValid section14Catalog 1 (⟨228,(15),[1,2,5,6,13,14],[170],802⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3620 : RecordDataValid section14Catalog 1 (⟨228,(16),[1,2,5,6,13,14],[170],803⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3621 : RecordDataValid section14Catalog 1 (⟨228,(17),[1,2,5,6,13,14],[170],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3622 : RecordDataValid section14Catalog 1 (⟨228,(18),[1,2,5,6,13,14],[170],805⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3623 : RecordDataValid section14Catalog 1 (⟨228,(19),[1,2,5,6,13,14],[170],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3624 : RecordDataValid section14Catalog 1 (⟨228,(20),[1,2,5,6,13,14],[170],806⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3625 : RecordDataValid section14Catalog 1 (⟨228,(21),[1,2,5,6,13,14],[170],807⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3626 : RecordDataValid section14Catalog 1 (⟨228,(22),[1,2,5,6,13,14],[170],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3627 : RecordDataValid section14Catalog 1 (⟨228,(23),[1,2,5,6,13,14],[170],809⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3628 : RecordDataValid section14Catalog 1 (⟨228,(24),[1,2,5,6,13,14],[170],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3629 : RecordDataValid section14Catalog 1 (⟨230,(0),[1,2,5,6,13,14],[170],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3630 : RecordDataValid section14Catalog 1 (⟨230,(1),[1,2,5,6,13,14],[170],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3631 : RecordDataValid section14Catalog 1 (⟨230,(2),[1,2,5,6,13,14],[170],812⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3632 : RecordDataValid section14Catalog 1 (⟨230,(3),[1,2,5,6,13,14],[170],813⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3633 : RecordDataValid section14Catalog 1 (⟨230,(4),[1,2,5,6,13,14],[170],814⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨814,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],815⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3634 : RecordDataValid section14Catalog 1 (⟨230,(5),[1,2,5,6,13,14],[170],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3635 : RecordDataValid section14Catalog 1 (⟨230,(6),[1,2,5,6,13,14],[170],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3636 : RecordDataValid section14Catalog 1 (⟨230,(7),[1,5,6,13],[170],815⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨815,[1,4,5,6,8,9,10,12,13,16],816⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3637 : RecordDataValid section14Catalog 1 (⟨230,(8),[1,2,5,6,13,14],[170],816⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3638 : RecordDataValid section14Catalog 1 (⟨230,(9),[1,2,6,13,14],[170],817⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3639 : RecordDataValid section14Catalog 1 (⟨230,(10),[1,2,5,6,13,14],[170],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3640 : RecordDataValid section14Catalog 1 (⟨230,(11),[1,2,5,6,13,14],[170],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3641 : RecordDataValid section14Catalog 1 (⟨230,(12),[1,5,13],[170],820⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨820,[1,4,5,8,9,10,12,13,16],821⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3642 : RecordDataValid section14Catalog 1 (⟨230,(13),[1,2,5,6,13,14],[170],821⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨821,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],822⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3643 : RecordDataValid section14Catalog 1 (⟨230,(14),[1,2,6,13,14],[170],817⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3644 : RecordDataValid section14Catalog 1 (⟨230,(15),[1,2,5,6,13,14],[170],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3645 : RecordDataValid section14Catalog 1 (⟨230,(16),[1,2,5,6,13,14],[170],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3646 : RecordDataValid section14Catalog 1 (⟨230,(17),[1,2,5,6,13,14],[170],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3647 : RecordDataValid section14Catalog 1 (⟨230,(18),[1,2,5,6,13,14],[170],825⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨825,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],826⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3616_3648 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3616).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3616).take 32 = [⟨228,(12),[1,2,5,6,13,14],[170],800⟩,⟨228,(13),[1,2,5,6,13,14],[170],801⟩,⟨228,(14),[1,2,5,6,13,14],[170],800⟩,⟨228,(15),[1,2,5,6,13,14],[170],802⟩,⟨228,(16),[1,2,5,6,13,14],[170],803⟩,⟨228,(17),[1,2,5,6,13,14],[170],804⟩,⟨228,(18),[1,2,5,6,13,14],[170],805⟩,⟨228,(19),[1,2,5,6,13,14],[170],804⟩,⟨228,(20),[1,2,5,6,13,14],[170],806⟩,⟨228,(21),[1,2,5,6,13,14],[170],807⟩,⟨228,(22),[1,2,5,6,13,14],[170],808⟩,⟨228,(23),[1,2,5,6,13,14],[170],809⟩,⟨228,(24),[1,2,5,6,13,14],[170],808⟩,⟨230,(0),[1,2,5,6,13,14],[170],810⟩,⟨230,(1),[1,2,5,6,13,14],[170],811⟩,⟨230,(2),[1,2,5,6,13,14],[170],812⟩,⟨230,(3),[1,2,5,6,13,14],[170],813⟩,⟨230,(4),[1,2,5,6,13,14],[170],814⟩,⟨230,(5),[1,2,5,6,13,14],[170],810⟩,⟨230,(6),[1,2,5,6,13,14],[170],811⟩,⟨230,(7),[1,5,6,13],[170],815⟩,⟨230,(8),[1,2,5,6,13,14],[170],816⟩,⟨230,(9),[1,2,6,13,14],[170],817⟩,⟨230,(10),[1,2,5,6,13,14],[170],818⟩,⟨230,(11),[1,2,5,6,13,14],[170],819⟩,⟨230,(12),[1,5,13],[170],820⟩,⟨230,(13),[1,2,5,6,13,14],[170],821⟩,⟨230,(14),[1,2,6,13,14],[170],817⟩,⟨230,(15),[1,2,5,6,13,14],[170],822⟩,⟨230,(16),[1,2,5,6,13,14],[170],823⟩,⟨230,(17),[1,2,5,6,13,14],[170],824⟩,⟨230,(18),[1,2,5,6,13,14],[170],825⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3616
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3617
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3618
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3619
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3620
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3621
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3622
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3623
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3624
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3625
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3626
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3627
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3628
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3629
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3630
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3631
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3632
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3633
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3634
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3635
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3636
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3637
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3638
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3639
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3640
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3641
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3642
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3643
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3644
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3645
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3646
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3647
end Section14Records_1_3616_3648

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3616_3648

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3584).take 64, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 3584 3616 3648 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_3584_3616 hnum) (Freiman.workReverse20260919_s0001_records_3616_3648 hnum))

#print axioms solution
