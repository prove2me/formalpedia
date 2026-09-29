-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3520_3552
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:02:34.239314+00:00
-- url     : https://prove2.me/submissions/54fc4ae3-9863-446d-917e-31fe41bc1516

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
namespace Section14Records_5_3520_3552
private theorem valid3520 : RecordDataValid section14Catalog 5 (⟨221,(22),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3521 : RecordDataValid section14Catalog 5 (⟨221,(22),[5,6],[174],1043⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1043,[3,5,6,7],1047⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3522 : RecordDataValid section14Catalog 5 (⟨221,(23),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3523 : RecordDataValid section14Catalog 5 (⟨221,(23),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3524 : RecordDataValid section14Catalog 5 (⟨221,(24),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3525 : RecordDataValid section14Catalog 5 (⟨221,(24),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3526 : RecordDataValid section14Catalog 5 (⟨222,(0),[5],[170,174],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3527 : RecordDataValid section14Catalog 5 (⟨222,(1),[1,2,5,6,13,14],[170],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3528 : RecordDataValid section14Catalog 5 (⟨222,(1),[5,6],[174],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3529 : RecordDataValid section14Catalog 5 (⟨222,(2),[1,2,5,6,13,14],[170],737⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨737,[1,2,3,4,5,6,7,10,11,13,14,15,16],738⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3530 : RecordDataValid section14Catalog 5 (⟨222,(2),[5,6],[174],737⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨737,[1,2,3,4,5,6,7,10,11,13,14,15,16],738⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3531 : RecordDataValid section14Catalog 5 (⟨222,(3),[1,2,5,6,13,14],[170],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3532 : RecordDataValid section14Catalog 5 (⟨222,(3),[5,6],[174],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3533 : RecordDataValid section14Catalog 5 (⟨222,(4),[1,2,5,6,13,14],[170],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3534 : RecordDataValid section14Catalog 5 (⟨222,(4),[5,6],[174],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3535 : RecordDataValid section14Catalog 5 (⟨222,(5),[1,2,5,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3536 : RecordDataValid section14Catalog 5 (⟨222,(5),[5,6],[174],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3537 : RecordDataValid section14Catalog 5 (⟨222,(6),[5],[170,174],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3538 : RecordDataValid section14Catalog 5 (⟨222,(7),[1,2,5,6,13,14],[170],739⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨739,[1,2,3,4,5,6,7,10,11,13,14,15,16],740⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3539 : RecordDataValid section14Catalog 5 (⟨222,(7),[5,6],[174],739⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨739,[1,2,3,4,5,6,7,10,11,13,14,15,16],740⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3540 : RecordDataValid section14Catalog 5 (⟨222,(8),[1,2,5,6,13,14],[170],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3541 : RecordDataValid section14Catalog 5 (⟨222,(8),[5,6],[174],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3542 : RecordDataValid section14Catalog 5 (⟨222,(9),[1,2,5,6,13,14],[170],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3543 : RecordDataValid section14Catalog 5 (⟨222,(9),[5,6],[174],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3544 : RecordDataValid section14Catalog 5 (⟨222,(10),[5],[170,174],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3545 : RecordDataValid section14Catalog 5 (⟨222,(11),[5],[170,174],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3546 : RecordDataValid section14Catalog 5 (⟨222,(12),[5],[170,174],1361⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1361,[4,5,10,16],1365⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3547 : RecordDataValid section14Catalog 5 (⟨222,(13),[5],[170,174],1362⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1362,[4,5,8,9,12,16],1366⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3548 : RecordDataValid section14Catalog 5 (⟨222,(14),[1,2,5,6,13,14],[170],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3549 : RecordDataValid section14Catalog 5 (⟨222,(14),[5,6],[174],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3550 : RecordDataValid section14Catalog 5 (⟨222,(15),[1,2,5,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3551 : RecordDataValid section14Catalog 5 (⟨222,(15),[5,6],[174],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3520).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3520).take 32 = [⟨221,(22),[1,2,5,6,13,14],[170],522⟩,⟨221,(22),[5,6],[174],1043⟩,⟨221,(23),[1,2,5,6,13,14],[170],517⟩,⟨221,(23),[5,6],[174],1038⟩,⟨221,(24),[1,2,5,6,13,14],[170],518⟩,⟨221,(24),[5,6],[174],1039⟩,⟨222,(0),[5],[170,174],736⟩,⟨222,(1),[1,2,5,6,13,14],[170],736⟩,⟨222,(1),[5,6],[174],736⟩,⟨222,(2),[1,2,5,6,13,14],[170],737⟩,⟨222,(2),[5,6],[174],737⟩,⟨222,(3),[1,2,5,6,13,14],[170],736⟩,⟨222,(3),[5,6],[174],736⟩,⟨222,(4),[1,2,5,6,13,14],[170],525⟩,⟨222,(4),[5,6],[174],525⟩,⟨222,(5),[1,2,5,6,13,14],[170],735⟩,⟨222,(5),[5,6],[174],735⟩,⟨222,(6),[5],[170,174],740⟩,⟨222,(7),[1,2,5,6,13,14],[170],739⟩,⟨222,(7),[5,6],[174],739⟩,⟨222,(8),[1,2,5,6,13,14],[170],740⟩,⟨222,(8),[5,6],[174],740⟩,⟨222,(9),[1,2,5,6,13,14],[170],528⟩,⟨222,(9),[5,6],[174],528⟩,⟨222,(10),[5],[170,174],735⟩,⟨222,(11),[5],[170,174],738⟩,⟨222,(12),[5],[170,174],1361⟩,⟨222,(13),[5],[170,174],1362⟩,⟨222,(14),[1,2,5,6,13,14],[170],531⟩,⟨222,(14),[5,6],[174],531⟩,⟨222,(15),[1,2,5,6,13,14],[170],735⟩,⟨222,(15),[5,6],[174],735⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3520
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3521
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3522
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3523
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3524
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3525
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3526
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3527
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3528
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3529
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3530
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3531
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3532
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3533
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3534
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3535
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3536
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3537
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3538
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3539
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3540
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3541
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3542
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3543
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3544
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3545
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3546
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3547
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3548
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3549
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3550
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3551
end Section14Records_5_3520_3552

#print axioms solution
