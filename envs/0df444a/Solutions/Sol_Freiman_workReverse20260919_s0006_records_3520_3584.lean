-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3520_3584
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:31:48.773524+00:00
-- url     : https://prove2.me/submissions/4951b36e-f4fd-463c-8c43-bbcfb701ae34

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3520_3552
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3520_3552
private theorem valid3520 : RecordDataValid section14Catalog 6 (⟨230,(7),[5,6],[174],1063⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1063,[3,5,6,7],1067⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3521 : RecordDataValid section14Catalog 6 (⟨230,(8),[1,2,5,6,13,14],[170],816⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3522 : RecordDataValid section14Catalog 6 (⟨230,(8),[5,6],[174],816⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3523 : RecordDataValid section14Catalog 6 (⟨230,(9),[1,2,6,13,14],[170],817⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3524 : RecordDataValid section14Catalog 6 (⟨230,(9),[5,6],[174],1065⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1065,[3,5,6,7],1069⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3525 : RecordDataValid section14Catalog 6 (⟨230,(10),[1,2,5,6,13,14],[170],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3526 : RecordDataValid section14Catalog 6 (⟨230,(10),[5,6],[174],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3527 : RecordDataValid section14Catalog 6 (⟨230,(11),[1,2,5,6,13,14],[170],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3528 : RecordDataValid section14Catalog 6 (⟨230,(11),[5,6],[174],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3529 : RecordDataValid section14Catalog 6 (⟨230,(12),[2,6,14],[170],923⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨923,[2,3,6,7,11,14,15],927⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3530 : RecordDataValid section14Catalog 6 (⟨230,(12),[5,6],[174],1066⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1066,[3,5,6,7],1070⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3531 : RecordDataValid section14Catalog 6 (⟨230,(13),[1,2,5,6,13,14],[170],821⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨821,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],822⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3532 : RecordDataValid section14Catalog 6 (⟨230,(13),[5,6],[174],1066⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1066,[3,5,6,7],1070⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3533 : RecordDataValid section14Catalog 6 (⟨230,(14),[1,2,6,13,14],[170],817⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3534 : RecordDataValid section14Catalog 6 (⟨230,(14),[5,6],[174],1065⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1065,[3,5,6,7],1069⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3535 : RecordDataValid section14Catalog 6 (⟨230,(15),[1,2,5,6,13,14],[170],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3536 : RecordDataValid section14Catalog 6 (⟨230,(15),[5,6],[174],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3537 : RecordDataValid section14Catalog 6 (⟨230,(16),[1,2,5,6,13,14],[170],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3538 : RecordDataValid section14Catalog 6 (⟨230,(16),[5,6],[174],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3539 : RecordDataValid section14Catalog 6 (⟨230,(17),[1,2,5,6,13,14],[170],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3540 : RecordDataValid section14Catalog 6 (⟨230,(17),[5,6],[174],1067⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1067,[3,5,6,7],1071⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3541 : RecordDataValid section14Catalog 6 (⟨230,(18),[1,2,5,6,13,14],[170],825⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨825,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],826⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3542 : RecordDataValid section14Catalog 6 (⟨230,(18),[5,6],[174],1067⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1067,[3,5,6,7],1071⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3543 : RecordDataValid section14Catalog 6 (⟨230,(19),[1,2,5,6,13,14],[170],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3544 : RecordDataValid section14Catalog 6 (⟨230,(19),[5,6],[174],1067⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1067,[3,5,6,7],1071⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3545 : RecordDataValid section14Catalog 6 (⟨230,(20),[1,2,5,6,13,14],[170],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3546 : RecordDataValid section14Catalog 6 (⟨230,(20),[5,6],[174],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3547 : RecordDataValid section14Catalog 6 (⟨230,(21),[1,2,5,6,13,14],[170],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3548 : RecordDataValid section14Catalog 6 (⟨230,(21),[5,6],[174],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3549 : RecordDataValid section14Catalog 6 (⟨230,(22),[1,2,5,6,13,14],[170],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3550 : RecordDataValid section14Catalog 6 (⟨230,(22),[5,6],[174],1068⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1068,[3,5,6,7],1072⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3551 : RecordDataValid section14Catalog 6 (⟨230,(23),[1,2,5,6,13,14],[170],829⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3520_3552 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3520).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3520).take 32 = [⟨230,(7),[5,6],[174],1063⟩,⟨230,(8),[1,2,5,6,13,14],[170],816⟩,⟨230,(8),[5,6],[174],816⟩,⟨230,(9),[1,2,6,13,14],[170],817⟩,⟨230,(9),[5,6],[174],1065⟩,⟨230,(10),[1,2,5,6,13,14],[170],818⟩,⟨230,(10),[5,6],[174],818⟩,⟨230,(11),[1,2,5,6,13,14],[170],819⟩,⟨230,(11),[5,6],[174],819⟩,⟨230,(12),[2,6,14],[170],923⟩,⟨230,(12),[5,6],[174],1066⟩,⟨230,(13),[1,2,5,6,13,14],[170],821⟩,⟨230,(13),[5,6],[174],1066⟩,⟨230,(14),[1,2,6,13,14],[170],817⟩,⟨230,(14),[5,6],[174],1065⟩,⟨230,(15),[1,2,5,6,13,14],[170],822⟩,⟨230,(15),[5,6],[174],822⟩,⟨230,(16),[1,2,5,6,13,14],[170],823⟩,⟨230,(16),[5,6],[174],823⟩,⟨230,(17),[1,2,5,6,13,14],[170],824⟩,⟨230,(17),[5,6],[174],1067⟩,⟨230,(18),[1,2,5,6,13,14],[170],825⟩,⟨230,(18),[5,6],[174],1067⟩,⟨230,(19),[1,2,5,6,13,14],[170],824⟩,⟨230,(19),[5,6],[174],1067⟩,⟨230,(20),[1,2,5,6,13,14],[170],826⟩,⟨230,(20),[5,6],[174],826⟩,⟨230,(21),[1,2,5,6,13,14],[170],827⟩,⟨230,(21),[5,6],[174],827⟩,⟨230,(22),[1,2,5,6,13,14],[170],828⟩,⟨230,(22),[5,6],[174],1068⟩,⟨230,(23),[1,2,5,6,13,14],[170],829⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3520
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3521
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3522
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3523
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3524
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3525
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3526
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3527
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3528
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3529
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3530
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3531
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3532
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3533
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3534
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3535
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3536
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3537
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3538
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3539
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3540
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3541
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3542
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3543
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3544
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3545
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3546
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3547
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3548
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3549
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3550
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3551
end Section14Records_6_3520_3552

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3520_3552


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3552_3584
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3552_3584
private theorem valid3552 : RecordDataValid section14Catalog 6 (⟨230,(23),[5,6],[174],1068⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1068,[3,5,6,7],1072⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3553 : RecordDataValid section14Catalog 6 (⟨230,(24),[1,2,5,6,13,14],[170],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3554 : RecordDataValid section14Catalog 6 (⟨230,(24),[5,6],[174],1068⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1068,[3,5,6,7],1072⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3555 : RecordDataValid section14Catalog 6 (⟨231,(0),[1,2,5,6,13,14],[170],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3556 : RecordDataValid section14Catalog 6 (⟨231,(0),[5,6],[174],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3557 : RecordDataValid section14Catalog 6 (⟨231,(1),[1,2,5,6,13,14],[170],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3558 : RecordDataValid section14Catalog 6 (⟨231,(1),[5,6],[174],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3559 : RecordDataValid section14Catalog 6 (⟨231,(2),[1,2,5,6,13,14],[170],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3560 : RecordDataValid section14Catalog 6 (⟨231,(2),[5,6],[174],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3561 : RecordDataValid section14Catalog 6 (⟨231,(3),[1,2,5,6,13,14],[170],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3562 : RecordDataValid section14Catalog 6 (⟨231,(3),[5,6],[174],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3563 : RecordDataValid section14Catalog 6 (⟨231,(4),[1,2,5,6,13,14],[170],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3564 : RecordDataValid section14Catalog 6 (⟨231,(4),[5,6],[174],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3565 : RecordDataValid section14Catalog 6 (⟨231,(5),[1,2,5,6,13,14],[170],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3566 : RecordDataValid section14Catalog 6 (⟨231,(5),[5,6],[174],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3567 : RecordDataValid section14Catalog 6 (⟨231,(6),[1,2,5,6,13,14],[170],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3568 : RecordDataValid section14Catalog 6 (⟨231,(6),[5,6],[174],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3569 : RecordDataValid section14Catalog 6 (⟨231,(7),[1,2,5,6,13,14],[170],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3570 : RecordDataValid section14Catalog 6 (⟨231,(7),[5,6],[174],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3571 : RecordDataValid section14Catalog 6 (⟨231,(8),[1,2,5,6,13,14],[170],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3572 : RecordDataValid section14Catalog 6 (⟨231,(8),[5,6],[174],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3573 : RecordDataValid section14Catalog 6 (⟨231,(9),[1,2,5,6,13,14],[170],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3574 : RecordDataValid section14Catalog 6 (⟨231,(9),[5,6],[174],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3575 : RecordDataValid section14Catalog 6 (⟨231,(10),[1,2,5,6,13,14],[170],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3576 : RecordDataValid section14Catalog 6 (⟨231,(10),[5,6],[174],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3577 : RecordDataValid section14Catalog 6 (⟨231,(11),[1,2,5,6,13,14],[170],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3578 : RecordDataValid section14Catalog 6 (⟨231,(11),[5,6],[174],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3579 : RecordDataValid section14Catalog 6 (⟨231,(12),[1,2,5,6,13,14],[170],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3580 : RecordDataValid section14Catalog 6 (⟨231,(12),[5,6],[174],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3581 : RecordDataValid section14Catalog 6 (⟨231,(13),[1,2,5,6,13,14],[170],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3582 : RecordDataValid section14Catalog 6 (⟨231,(13),[5,6],[174],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3583 : RecordDataValid section14Catalog 6 (⟨231,(14),[1,2,5,6,13,14],[170],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3552_3584 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3552).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3552).take 32 = [⟨230,(23),[5,6],[174],1068⟩,⟨230,(24),[1,2,5,6,13,14],[170],828⟩,⟨230,(24),[5,6],[174],1068⟩,⟨231,(0),[1,2,5,6,13,14],[170],830⟩,⟨231,(0),[5,6],[174],830⟩,⟨231,(1),[1,2,5,6,13,14],[170],831⟩,⟨231,(1),[5,6],[174],831⟩,⟨231,(2),[1,2,5,6,13,14],[170],832⟩,⟨231,(2),[5,6],[174],832⟩,⟨231,(3),[1,2,5,6,13,14],[170],833⟩,⟨231,(3),[5,6],[174],833⟩,⟨231,(4),[1,2,5,6,13,14],[170],830⟩,⟨231,(4),[5,6],[174],830⟩,⟨231,(5),[1,2,5,6,13,14],[170],831⟩,⟨231,(5),[5,6],[174],831⟩,⟨231,(6),[1,2,5,6,13,14],[170],832⟩,⟨231,(6),[5,6],[174],832⟩,⟨231,(7),[1,2,5,6,13,14],[170],833⟩,⟨231,(7),[5,6],[174],833⟩,⟨231,(8),[1,2,5,6,13,14],[170],834⟩,⟨231,(8),[5,6],[174],834⟩,⟨231,(9),[1,2,5,6,13,14],[170],835⟩,⟨231,(9),[5,6],[174],835⟩,⟨231,(10),[1,2,5,6,13,14],[170],836⟩,⟨231,(10),[5,6],[174],836⟩,⟨231,(11),[1,2,5,6,13,14],[170],837⟩,⟨231,(11),[5,6],[174],837⟩,⟨231,(12),[1,2,5,6,13,14],[170],838⟩,⟨231,(12),[5,6],[174],838⟩,⟨231,(13),[1,2,5,6,13,14],[170],839⟩,⟨231,(13),[5,6],[174],839⟩,⟨231,(14),[1,2,5,6,13,14],[170],838⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3552
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3553
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3554
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3555
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3556
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3557
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3558
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3559
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3560
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3561
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3562
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3563
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3564
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3565
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3566
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3567
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3568
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3569
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3570
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3571
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3572
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3573
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3574
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3575
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3576
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3577
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3578
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3579
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3580
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3581
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3582
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3583
end Section14Records_6_3552_3584

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3552_3584

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3520).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 3520 3552 3584 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3520_3552 hnum) (Freiman.workReverse20260919_s0006_records_3552_3584 hnum))

#print axioms solution
