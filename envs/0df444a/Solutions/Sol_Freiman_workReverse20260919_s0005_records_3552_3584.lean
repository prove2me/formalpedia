-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3552_3584
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:03:08.989404+00:00
-- url     : https://prove2.me/submissions/64e9ee84-e6b6-434f-8815-70af0b45fee8

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
namespace Section14Records_5_3552_3584
private theorem valid3552 : RecordDataValid section14Catalog 5 (⟨222,(16),[1,2,5,6,13,14],[170],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3553 : RecordDataValid section14Catalog 5 (⟨222,(16),[5,6],[174],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3554 : RecordDataValid section14Catalog 5 (⟨222,(17),[1,2,5,6,13,14],[170],745⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨745,[1,2,3,4,5,6,7,10,11,13,14,15,16],746⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3555 : RecordDataValid section14Catalog 5 (⟨222,(17),[5,6],[174],745⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨745,[1,2,3,4,5,6,7,10,11,13,14,15,16],746⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3556 : RecordDataValid section14Catalog 5 (⟨222,(18),[1,2,5,6,13,14],[170],746⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨746,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],747⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3557 : RecordDataValid section14Catalog 5 (⟨222,(18),[5,6],[174],746⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨746,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],747⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3558 : RecordDataValid section14Catalog 5 (⟨222,(19),[1,2,5,6,13,14],[170],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3559 : RecordDataValid section14Catalog 5 (⟨222,(19),[5,6],[174],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3560 : RecordDataValid section14Catalog 5 (⟨222,(20),[1,2,5,6,13,14],[170],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3561 : RecordDataValid section14Catalog 5 (⟨222,(20),[5,6],[174],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3562 : RecordDataValid section14Catalog 5 (⟨222,(21),[1,2,5,6,13,14],[170],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3563 : RecordDataValid section14Catalog 5 (⟨222,(21),[5,6],[174],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3564 : RecordDataValid section14Catalog 5 (⟨222,(22),[1,2,5,6,13,14],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3565 : RecordDataValid section14Catalog 5 (⟨222,(22),[5,6],[174],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3566 : RecordDataValid section14Catalog 5 (⟨222,(23),[1,2,5,6,13,14],[170],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3567 : RecordDataValid section14Catalog 5 (⟨222,(23),[5,6],[174],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3568 : RecordDataValid section14Catalog 5 (⟨222,(24),[1,2,5,6,13,14],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3569 : RecordDataValid section14Catalog 5 (⟨222,(24),[5,6],[174],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3570 : RecordDataValid section14Catalog 5 (⟨224,(0),[1,2,5,6,13,14],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3571 : RecordDataValid section14Catalog 5 (⟨224,(0),[5,6],[174],1044⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1044,[3,5,6,7],1048⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3572 : RecordDataValid section14Catalog 5 (⟨224,(1),[1,2,5,6,13,14],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3573 : RecordDataValid section14Catalog 5 (⟨224,(1),[5,6],[174],1044⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1044,[3,5,6,7],1048⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3574 : RecordDataValid section14Catalog 5 (⟨224,(2),[1,2,5,6,13,14],[170],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3575 : RecordDataValid section14Catalog 5 (⟨224,(2),[5,6],[174],1045⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1045,[3,5,6,7],1049⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3576 : RecordDataValid section14Catalog 5 (⟨224,(3),[1,2,5,6,13,14],[170],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3577 : RecordDataValid section14Catalog 5 (⟨224,(3),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3578 : RecordDataValid section14Catalog 5 (⟨224,(4),[1,2,5,6,13,14],[170],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3579 : RecordDataValid section14Catalog 5 (⟨224,(4),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3580 : RecordDataValid section14Catalog 5 (⟨224,(5),[1,2,5,6,13,14],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3581 : RecordDataValid section14Catalog 5 (⟨224,(5),[5,6],[174],1046⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1046,[3,5,6,7],1050⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3582 : RecordDataValid section14Catalog 5 (⟨224,(6),[1,2,5,6,13,14],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3583 : RecordDataValid section14Catalog 5 (⟨224,(6),[5,6],[174],1046⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1046,[3,5,6,7],1050⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3552).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3552).take 32 = [⟨222,(16),[1,2,5,6,13,14],[170],738⟩,⟨222,(16),[5,6],[174],738⟩,⟨222,(17),[1,2,5,6,13,14],[170],745⟩,⟨222,(17),[5,6],[174],745⟩,⟨222,(18),[1,2,5,6,13,14],[170],746⟩,⟨222,(18),[5,6],[174],746⟩,⟨222,(19),[1,2,5,6,13,14],[170],534⟩,⟨222,(19),[5,6],[174],534⟩,⟨222,(20),[1,2,5,6,13,14],[170],535⟩,⟨222,(20),[5,6],[174],535⟩,⟨222,(21),[1,2,5,6,13,14],[170],536⟩,⟨222,(21),[5,6],[174],536⟩,⟨222,(22),[1,2,5,6,13,14],[170],537⟩,⟨222,(22),[5,6],[174],537⟩,⟨222,(23),[1,2,5,6,13,14],[170],538⟩,⟨222,(23),[5,6],[174],538⟩,⟨222,(24),[1,2,5,6,13,14],[170],537⟩,⟨222,(24),[5,6],[174],537⟩,⟨224,(0),[1,2,5,6,13,14],[170],539⟩,⟨224,(0),[5,6],[174],1044⟩,⟨224,(1),[1,2,5,6,13,14],[170],539⟩,⟨224,(1),[5,6],[174],1044⟩,⟨224,(2),[1,2,5,6,13,14],[170],540⟩,⟨224,(2),[5,6],[174],1045⟩,⟨224,(3),[1,2,5,6,13,14],[170],541⟩,⟨224,(3),[5,6],[174],1038⟩,⟨224,(4),[1,2,5,6,13,14],[170],542⟩,⟨224,(4),[5,6],[174],1039⟩,⟨224,(5),[1,2,5,6,13,14],[170],543⟩,⟨224,(5),[5,6],[174],1046⟩,⟨224,(6),[1,2,5,6,13,14],[170],543⟩,⟨224,(6),[5,6],[174],1046⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3552
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3553
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3554
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3555
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3556
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3557
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3558
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3559
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3560
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3561
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3562
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3563
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3564
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3565
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3566
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3567
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3568
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3569
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3570
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3571
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3572
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3573
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3574
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3575
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3576
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3577
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3578
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3579
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3580
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3581
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3582
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3583
end Section14Records_5_3552_3584

#print axioms solution
