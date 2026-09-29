-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3584_3616
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:03:14.855821+00:00
-- url     : https://prove2.me/submissions/2daacee4-ca40-4515-ae3f-145937c7b77f

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
namespace Section14Records_5_3584_3616
private theorem valid3584 : RecordDataValid section14Catalog 5 (⟨224,(7),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3585 : RecordDataValid section14Catalog 5 (⟨224,(7),[5,6],[174],1045⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1045,[3,5,6,7],1049⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3586 : RecordDataValid section14Catalog 5 (⟨224,(8),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3587 : RecordDataValid section14Catalog 5 (⟨224,(8),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3588 : RecordDataValid section14Catalog 5 (⟨224,(9),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3589 : RecordDataValid section14Catalog 5 (⟨224,(9),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3590 : RecordDataValid section14Catalog 5 (⟨224,(10),[1,2,5,6,13,14],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3591 : RecordDataValid section14Catalog 5 (⟨224,(10),[5,6],[174],1044⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1044,[3,5,6,7],1048⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3592 : RecordDataValid section14Catalog 5 (⟨224,(11),[1,2,5,6,13,14],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3593 : RecordDataValid section14Catalog 5 (⟨224,(11),[5,6],[174],1044⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1044,[3,5,6,7],1048⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3594 : RecordDataValid section14Catalog 5 (⟨224,(12),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3595 : RecordDataValid section14Catalog 5 (⟨224,(12),[5,6],[174],1045⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1045,[3,5,6,7],1049⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3596 : RecordDataValid section14Catalog 5 (⟨224,(13),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3597 : RecordDataValid section14Catalog 5 (⟨224,(13),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3598 : RecordDataValid section14Catalog 5 (⟨224,(14),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3599 : RecordDataValid section14Catalog 5 (⟨224,(14),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3600 : RecordDataValid section14Catalog 5 (⟨224,(15),[1,2,5,6,13,14],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3601 : RecordDataValid section14Catalog 5 (⟨224,(15),[5,6],[174],1047⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1047,[3,5,6,7],1051⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3602 : RecordDataValid section14Catalog 5 (⟨224,(16),[1,2,5,6,13,14],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3603 : RecordDataValid section14Catalog 5 (⟨224,(16),[5,6],[174],1047⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1047,[3,5,6,7],1051⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3604 : RecordDataValid section14Catalog 5 (⟨224,(17),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3605 : RecordDataValid section14Catalog 5 (⟨224,(17),[5,6],[174],1045⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1045,[3,5,6,7],1049⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3606 : RecordDataValid section14Catalog 5 (⟨224,(18),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3607 : RecordDataValid section14Catalog 5 (⟨224,(18),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3608 : RecordDataValid section14Catalog 5 (⟨224,(19),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3609 : RecordDataValid section14Catalog 5 (⟨224,(19),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3610 : RecordDataValid section14Catalog 5 (⟨224,(20),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3611 : RecordDataValid section14Catalog 5 (⟨224,(20),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3612 : RecordDataValid section14Catalog 5 (⟨224,(21),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3613 : RecordDataValid section14Catalog 5 (⟨224,(21),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3614 : RecordDataValid section14Catalog 5 (⟨224,(22),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3615 : RecordDataValid section14Catalog 5 (⟨224,(22),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3584).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3584).take 32 = [⟨224,(7),[1,2,5,6,13,14],[170],544⟩,⟨224,(7),[5,6],[174],1045⟩,⟨224,(8),[1,2,5,6,13,14],[170],517⟩,⟨224,(8),[5,6],[174],1038⟩,⟨224,(9),[1,2,5,6,13,14],[170],518⟩,⟨224,(9),[5,6],[174],1039⟩,⟨224,(10),[1,2,5,6,13,14],[170],545⟩,⟨224,(10),[5,6],[174],1044⟩,⟨224,(11),[1,2,5,6,13,14],[170],545⟩,⟨224,(11),[5,6],[174],1044⟩,⟨224,(12),[1,2,5,6,13,14],[170],544⟩,⟨224,(12),[5,6],[174],1045⟩,⟨224,(13),[1,2,5,6,13,14],[170],517⟩,⟨224,(13),[5,6],[174],1038⟩,⟨224,(14),[1,2,5,6,13,14],[170],518⟩,⟨224,(14),[5,6],[174],1039⟩,⟨224,(15),[1,2,5,6,13,14],[170],546⟩,⟨224,(15),[5,6],[174],1047⟩,⟨224,(16),[1,2,5,6,13,14],[170],546⟩,⟨224,(16),[5,6],[174],1047⟩,⟨224,(17),[1,2,5,6,13,14],[170],544⟩,⟨224,(17),[5,6],[174],1045⟩,⟨224,(18),[1,2,5,6,13,14],[170],517⟩,⟨224,(18),[5,6],[174],1038⟩,⟨224,(19),[1,2,5,6,13,14],[170],518⟩,⟨224,(19),[5,6],[174],1039⟩,⟨224,(20),[1,2,5,6,13,14],[170],547⟩,⟨224,(20),[5,6],[174],1048⟩,⟨224,(21),[1,2,5,6,13,14],[170],547⟩,⟨224,(21),[5,6],[174],1048⟩,⟨224,(22),[1,2,5,6,13,14],[170],547⟩,⟨224,(22),[5,6],[174],1048⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3584
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3585
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3586
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3587
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3588
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3589
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3590
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3591
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3592
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3593
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3594
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3595
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3596
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3597
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3598
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3599
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3600
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3601
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3602
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3603
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3604
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3605
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3606
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3607
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3608
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3609
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3610
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3611
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3612
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3613
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3614
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3615
end Section14Records_5_3584_3616

#print axioms solution
