-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3456_3488
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:09:52.335946+00:00
-- url     : https://prove2.me/submissions/d69f9a45-9d27-4f6b-b9e8-ae8cbf776ec4

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
namespace Section14Records_5_3456_3488
private theorem valid3456 : RecordDataValid section14Catalog 5 (⟨220,(10),[1,2,5,6,13,14],[170],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3457 : RecordDataValid section14Catalog 5 (⟨220,(10),[5,6],[174],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3458 : RecordDataValid section14Catalog 5 (⟨220,(11),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3459 : RecordDataValid section14Catalog 5 (⟨220,(11),[5,6],[174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3460 : RecordDataValid section14Catalog 5 (⟨220,(12),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3461 : RecordDataValid section14Catalog 5 (⟨220,(12),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3462 : RecordDataValid section14Catalog 5 (⟨220,(13),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3463 : RecordDataValid section14Catalog 5 (⟨220,(13),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3464 : RecordDataValid section14Catalog 5 (⟨220,(14),[1,2,5,6,13,14],[170],513⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨513,[1,2,5,6,9,10,13,14],514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3465 : RecordDataValid section14Catalog 5 (⟨220,(14),[5,6],[174],513⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨513,[1,2,5,6,9,10,13,14],514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3466 : RecordDataValid section14Catalog 5 (⟨220,(15),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3467 : RecordDataValid section14Catalog 5 (⟨220,(15),[5,6],[174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3468 : RecordDataValid section14Catalog 5 (⟨220,(16),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3469 : RecordDataValid section14Catalog 5 (⟨220,(16),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3470 : RecordDataValid section14Catalog 5 (⟨220,(17),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3471 : RecordDataValid section14Catalog 5 (⟨220,(17),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3472 : RecordDataValid section14Catalog 5 (⟨220,(18),[1,2,5,6,13,14],[170],514⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨514,[1,2,4,5,6,8,9,10,12,13,14,16],515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3473 : RecordDataValid section14Catalog 5 (⟨220,(18),[5,6],[174],514⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨514,[1,2,4,5,6,8,9,10,12,13,14,16],515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3474 : RecordDataValid section14Catalog 5 (⟨220,(19),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3475 : RecordDataValid section14Catalog 5 (⟨220,(19),[5,6],[174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3476 : RecordDataValid section14Catalog 5 (⟨221,(0),[1,2,5,6,13,14],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3477 : RecordDataValid section14Catalog 5 (⟨221,(0),[5,6],[174],1036⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1036,[3,5,6,7],1040⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3478 : RecordDataValid section14Catalog 5 (⟨221,(1),[1,2,5,6,13,14],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3479 : RecordDataValid section14Catalog 5 (⟨221,(1),[5,6],[174],1036⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1036,[3,5,6,7],1040⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3480 : RecordDataValid section14Catalog 5 (⟨221,(2),[1,2,5,6,13,14],[170],516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨516,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3481 : RecordDataValid section14Catalog 5 (⟨221,(2),[5,6],[174],1037⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1037,[3,5,6,7],1041⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3482 : RecordDataValid section14Catalog 5 (⟨221,(3),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3483 : RecordDataValid section14Catalog 5 (⟨221,(3),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3484 : RecordDataValid section14Catalog 5 (⟨221,(4),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3485 : RecordDataValid section14Catalog 5 (⟨221,(4),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3486 : RecordDataValid section14Catalog 5 (⟨221,(5),[1,2,5,6,13,14],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3487 : RecordDataValid section14Catalog 5 (⟨221,(5),[5,6],[174],1036⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1036,[3,5,6,7],1040⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3456).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3456).take 32 = [⟨220,(10),[1,2,5,6,13,14],[170],512⟩,⟨220,(10),[5,6],[174],512⟩,⟨220,(11),[1,2,5,6,13,14],[170],29⟩,⟨220,(11),[5,6],[174],29⟩,⟨220,(12),[1,2,5,6,13,14],[170],3⟩,⟨220,(12),[5,6],[174],3⟩,⟨220,(13),[1,2,5,6,13,14],[170],3⟩,⟨220,(13),[5,6],[174],3⟩,⟨220,(14),[1,2,5,6,13,14],[170],513⟩,⟨220,(14),[5,6],[174],513⟩,⟨220,(15),[1,2,5,6,13,14],[170],29⟩,⟨220,(15),[5,6],[174],29⟩,⟨220,(16),[1,2,5,6,13,14],[170],3⟩,⟨220,(16),[5,6],[174],3⟩,⟨220,(17),[1,2,5,6,13,14],[170],3⟩,⟨220,(17),[5,6],[174],3⟩,⟨220,(18),[1,2,5,6,13,14],[170],514⟩,⟨220,(18),[5,6],[174],514⟩,⟨220,(19),[1,2,5,6,13,14],[170],29⟩,⟨220,(19),[5,6],[174],29⟩,⟨221,(0),[1,2,5,6,13,14],[170],515⟩,⟨221,(0),[5,6],[174],1036⟩,⟨221,(1),[1,2,5,6,13,14],[170],515⟩,⟨221,(1),[5,6],[174],1036⟩,⟨221,(2),[1,2,5,6,13,14],[170],516⟩,⟨221,(2),[5,6],[174],1037⟩,⟨221,(3),[1,2,5,6,13,14],[170],517⟩,⟨221,(3),[5,6],[174],1038⟩,⟨221,(4),[1,2,5,6,13,14],[170],518⟩,⟨221,(4),[5,6],[174],1039⟩,⟨221,(5),[1,2,5,6,13,14],[170],515⟩,⟨221,(5),[5,6],[174],1036⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3456
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3457
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3458
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3459
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3460
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3461
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3462
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3463
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3464
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3465
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3466
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3467
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3468
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3469
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3470
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3471
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3472
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3473
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3474
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3475
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3476
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3477
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3478
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3479
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3480
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3481
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3482
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3483
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3484
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3485
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3486
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3487
end Section14Records_5_3456_3488

#print axioms solution
