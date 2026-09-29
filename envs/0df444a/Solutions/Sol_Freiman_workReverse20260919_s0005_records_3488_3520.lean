-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3488_3520
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:01:23.488365+00:00
-- url     : https://prove2.me/submissions/79b3ff10-0fa1-4e3f-8ef7-de90380720e8

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
namespace Section14Records_5_3488_3520
private theorem valid3488 : RecordDataValid section14Catalog 5 (⟨221,(6),[1,2,5,6,13,14],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3489 : RecordDataValid section14Catalog 5 (⟨221,(6),[5,6],[174],1036⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1036,[3,5,6,7],1040⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3490 : RecordDataValid section14Catalog 5 (⟨221,(7),[1,2,5,6,13,14],[170],516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨516,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3491 : RecordDataValid section14Catalog 5 (⟨221,(7),[5,6],[174],1037⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1037,[3,5,6,7],1041⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3492 : RecordDataValid section14Catalog 5 (⟨221,(8),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3493 : RecordDataValid section14Catalog 5 (⟨221,(8),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3494 : RecordDataValid section14Catalog 5 (⟨221,(9),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3495 : RecordDataValid section14Catalog 5 (⟨221,(9),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3496 : RecordDataValid section14Catalog 5 (⟨221,(10),[1,2,5,6,13,14],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3497 : RecordDataValid section14Catalog 5 (⟨221,(10),[5,6],[174],1040⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1040,[3,5,6,7],1044⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3498 : RecordDataValid section14Catalog 5 (⟨221,(11),[1,2,5,6,13,14],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3499 : RecordDataValid section14Catalog 5 (⟨221,(11),[5,6],[174],1040⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1040,[3,5,6,7],1044⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3500 : RecordDataValid section14Catalog 5 (⟨221,(12),[1,2,5,6,13,14],[170],520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨520,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],521⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3501 : RecordDataValid section14Catalog 5 (⟨221,(12),[5,6],[174],1041⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1041,[3,5,6,7],1045⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3502 : RecordDataValid section14Catalog 5 (⟨221,(13),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3503 : RecordDataValid section14Catalog 5 (⟨221,(13),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3504 : RecordDataValid section14Catalog 5 (⟨221,(14),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3505 : RecordDataValid section14Catalog 5 (⟨221,(14),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3506 : RecordDataValid section14Catalog 5 (⟨221,(15),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3507 : RecordDataValid section14Catalog 5 (⟨221,(15),[5,6],[174],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3508 : RecordDataValid section14Catalog 5 (⟨221,(16),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3509 : RecordDataValid section14Catalog 5 (⟨221,(16),[5,6],[174],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3510 : RecordDataValid section14Catalog 5 (⟨221,(17),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3511 : RecordDataValid section14Catalog 5 (⟨221,(17),[5,6],[174],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3512 : RecordDataValid section14Catalog 5 (⟨221,(18),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3513 : RecordDataValid section14Catalog 5 (⟨221,(18),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3514 : RecordDataValid section14Catalog 5 (⟨221,(19),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3515 : RecordDataValid section14Catalog 5 (⟨221,(19),[5,6],[174],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3516 : RecordDataValid section14Catalog 5 (⟨221,(20),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3517 : RecordDataValid section14Catalog 5 (⟨221,(20),[5,6],[174],1043⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1043,[3,5,6,7],1047⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3518 : RecordDataValid section14Catalog 5 (⟨221,(21),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3519 : RecordDataValid section14Catalog 5 (⟨221,(21),[5,6],[174],1043⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1043,[3,5,6,7],1047⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3488).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3488).take 32 = [⟨221,(6),[1,2,5,6,13,14],[170],515⟩,⟨221,(6),[5,6],[174],1036⟩,⟨221,(7),[1,2,5,6,13,14],[170],516⟩,⟨221,(7),[5,6],[174],1037⟩,⟨221,(8),[1,2,5,6,13,14],[170],517⟩,⟨221,(8),[5,6],[174],1038⟩,⟨221,(9),[1,2,5,6,13,14],[170],518⟩,⟨221,(9),[5,6],[174],1039⟩,⟨221,(10),[1,2,5,6,13,14],[170],519⟩,⟨221,(10),[5,6],[174],1040⟩,⟨221,(11),[1,2,5,6,13,14],[170],519⟩,⟨221,(11),[5,6],[174],1040⟩,⟨221,(12),[1,2,5,6,13,14],[170],520⟩,⟨221,(12),[5,6],[174],1041⟩,⟨221,(13),[1,2,5,6,13,14],[170],517⟩,⟨221,(13),[5,6],[174],1038⟩,⟨221,(14),[1,2,5,6,13,14],[170],518⟩,⟨221,(14),[5,6],[174],1039⟩,⟨221,(15),[1,2,5,6,13,14],[170],521⟩,⟨221,(15),[5,6],[174],1042⟩,⟨221,(16),[1,2,5,6,13,14],[170],521⟩,⟨221,(16),[5,6],[174],1042⟩,⟨221,(17),[1,2,5,6,13,14],[170],521⟩,⟨221,(17),[5,6],[174],1042⟩,⟨221,(18),[1,2,5,6,13,14],[170],517⟩,⟨221,(18),[5,6],[174],1038⟩,⟨221,(19),[1,2,5,6,13,14],[170],521⟩,⟨221,(19),[5,6],[174],1042⟩,⟨221,(20),[1,2,5,6,13,14],[170],522⟩,⟨221,(20),[5,6],[174],1043⟩,⟨221,(21),[1,2,5,6,13,14],[170],522⟩,⟨221,(21),[5,6],[174],1043⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3488
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3489
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3490
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3491
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3492
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3493
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3494
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3495
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3496
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3497
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3498
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3499
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3500
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3501
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3502
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3503
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3504
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3505
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3506
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3507
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3508
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3509
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3510
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3511
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3512
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3513
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3514
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3515
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3516
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3517
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3518
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3519
end Section14Records_5_3488_3520

#print axioms solution
