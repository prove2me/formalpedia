-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3456_3520
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:26:51.462375+00:00
-- url     : https://prove2.me/submissions/da957bb7-961a-4c71-9c1d-c210c8e93520

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3456_3488
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3456_3488
private theorem valid3456 : RecordDataValid section14Catalog 1 (⟨220,(7),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3457 : RecordDataValid section14Catalog 1 (⟨220,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3458 : RecordDataValid section14Catalog 1 (⟨220,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3459 : RecordDataValid section14Catalog 1 (⟨220,(10),[1,2,5,6,13,14],[170],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3460 : RecordDataValid section14Catalog 1 (⟨220,(11),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3461 : RecordDataValid section14Catalog 1 (⟨220,(12),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3462 : RecordDataValid section14Catalog 1 (⟨220,(13),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3463 : RecordDataValid section14Catalog 1 (⟨220,(14),[1,2,5,6,13,14],[170],513⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨513,[1,2,5,6,9,10,13,14],514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3464 : RecordDataValid section14Catalog 1 (⟨220,(15),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3465 : RecordDataValid section14Catalog 1 (⟨220,(16),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3466 : RecordDataValid section14Catalog 1 (⟨220,(17),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3467 : RecordDataValid section14Catalog 1 (⟨220,(18),[1,2,5,6,13,14],[170],514⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨514,[1,2,4,5,6,8,9,10,12,13,14,16],515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3468 : RecordDataValid section14Catalog 1 (⟨220,(19),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3469 : RecordDataValid section14Catalog 1 (⟨221,(0),[1,2,5,6,13,14],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3470 : RecordDataValid section14Catalog 1 (⟨221,(1),[1,2,5,6,13,14],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3471 : RecordDataValid section14Catalog 1 (⟨221,(2),[1,2,5,6,13,14],[170],516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨516,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3472 : RecordDataValid section14Catalog 1 (⟨221,(3),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3473 : RecordDataValid section14Catalog 1 (⟨221,(4),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3474 : RecordDataValid section14Catalog 1 (⟨221,(5),[1,2,5,6,13,14],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3475 : RecordDataValid section14Catalog 1 (⟨221,(6),[1,2,5,6,13,14],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3476 : RecordDataValid section14Catalog 1 (⟨221,(7),[1,2,5,6,13,14],[170],516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨516,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3477 : RecordDataValid section14Catalog 1 (⟨221,(8),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3478 : RecordDataValid section14Catalog 1 (⟨221,(9),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3479 : RecordDataValid section14Catalog 1 (⟨221,(10),[1,2,5,6,13,14],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3480 : RecordDataValid section14Catalog 1 (⟨221,(11),[1,2,5,6,13,14],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3481 : RecordDataValid section14Catalog 1 (⟨221,(12),[1,2,5,6,13,14],[170],520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨520,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],521⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3482 : RecordDataValid section14Catalog 1 (⟨221,(13),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3483 : RecordDataValid section14Catalog 1 (⟨221,(14),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3484 : RecordDataValid section14Catalog 1 (⟨221,(15),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3485 : RecordDataValid section14Catalog 1 (⟨221,(16),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3486 : RecordDataValid section14Catalog 1 (⟨221,(17),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3487 : RecordDataValid section14Catalog 1 (⟨221,(18),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3456_3488 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3456).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3456).take 32 = [⟨220,(7),[1,2,5,6,13,14],[170],29⟩,⟨220,(8),[1,2,5,6,13,14],[170],3⟩,⟨220,(9),[1,2,5,6,13,14],[170],3⟩,⟨220,(10),[1,2,5,6,13,14],[170],512⟩,⟨220,(11),[1,2,5,6,13,14],[170],29⟩,⟨220,(12),[1,2,5,6,13,14],[170],3⟩,⟨220,(13),[1,2,5,6,13,14],[170],3⟩,⟨220,(14),[1,2,5,6,13,14],[170],513⟩,⟨220,(15),[1,2,5,6,13,14],[170],29⟩,⟨220,(16),[1,2,5,6,13,14],[170],3⟩,⟨220,(17),[1,2,5,6,13,14],[170],3⟩,⟨220,(18),[1,2,5,6,13,14],[170],514⟩,⟨220,(19),[1,2,5,6,13,14],[170],29⟩,⟨221,(0),[1,2,5,6,13,14],[170],515⟩,⟨221,(1),[1,2,5,6,13,14],[170],515⟩,⟨221,(2),[1,2,5,6,13,14],[170],516⟩,⟨221,(3),[1,2,5,6,13,14],[170],517⟩,⟨221,(4),[1,2,5,6,13,14],[170],518⟩,⟨221,(5),[1,2,5,6,13,14],[170],515⟩,⟨221,(6),[1,2,5,6,13,14],[170],515⟩,⟨221,(7),[1,2,5,6,13,14],[170],516⟩,⟨221,(8),[1,2,5,6,13,14],[170],517⟩,⟨221,(9),[1,2,5,6,13,14],[170],518⟩,⟨221,(10),[1,2,5,6,13,14],[170],519⟩,⟨221,(11),[1,2,5,6,13,14],[170],519⟩,⟨221,(12),[1,2,5,6,13,14],[170],520⟩,⟨221,(13),[1,2,5,6,13,14],[170],517⟩,⟨221,(14),[1,2,5,6,13,14],[170],518⟩,⟨221,(15),[1,2,5,6,13,14],[170],521⟩,⟨221,(16),[1,2,5,6,13,14],[170],521⟩,⟨221,(17),[1,2,5,6,13,14],[170],521⟩,⟨221,(18),[1,2,5,6,13,14],[170],517⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3456
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3457
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3458
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3459
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3460
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3461
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3462
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3463
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3464
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3465
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3466
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3467
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3468
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3469
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3470
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3471
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3472
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3473
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3474
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3475
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3476
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3477
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3478
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3479
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3480
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3481
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3482
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3483
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3484
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3485
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3486
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3487
end Section14Records_1_3456_3488

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3456_3488


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3488_3520
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3488_3520
private theorem valid3488 : RecordDataValid section14Catalog 1 (⟨221,(19),[1,2,5,6,13,14],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3489 : RecordDataValid section14Catalog 1 (⟨221,(20),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3490 : RecordDataValid section14Catalog 1 (⟨221,(21),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3491 : RecordDataValid section14Catalog 1 (⟨221,(22),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3492 : RecordDataValid section14Catalog 1 (⟨221,(23),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3493 : RecordDataValid section14Catalog 1 (⟨221,(24),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3494 : RecordDataValid section14Catalog 1 (⟨222,(0),[1,2,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3495 : RecordDataValid section14Catalog 1 (⟨222,(1),[1,2,5,6,13,14],[170],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3496 : RecordDataValid section14Catalog 1 (⟨222,(2),[1,2,5,6,13,14],[170],737⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨737,[1,2,3,4,5,6,7,10,11,13,14,15,16],738⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3497 : RecordDataValid section14Catalog 1 (⟨222,(3),[1,2,5,6,13,14],[170],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3498 : RecordDataValid section14Catalog 1 (⟨222,(4),[1,2,5,6,13,14],[170],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3499 : RecordDataValid section14Catalog 1 (⟨222,(5),[1,2,5,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3500 : RecordDataValid section14Catalog 1 (⟨222,(6),[1,2,6,13,14],[170],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3501 : RecordDataValid section14Catalog 1 (⟨222,(7),[1,2,5,6,13,14],[170],739⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨739,[1,2,3,4,5,6,7,10,11,13,14,15,16],740⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3502 : RecordDataValid section14Catalog 1 (⟨222,(8),[1,2,5,6,13,14],[170],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3503 : RecordDataValid section14Catalog 1 (⟨222,(9),[1,2,5,6,13,14],[170],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3504 : RecordDataValid section14Catalog 1 (⟨222,(10),[1,2,6,13,14],[170],741⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨741,[1,2,3,6,7,10,11,13,14,15],742⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3505 : RecordDataValid section14Catalog 1 (⟨222,(11),[1,2,6,13,14],[170],742⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨742,[1,2,3,6,7,10,11,13,14,15],743⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3506 : RecordDataValid section14Catalog 1 (⟨222,(12),[1,2,6,13,14],[170],743⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨743,[1,2,3,6,7,11,13,14,15],744⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3507 : RecordDataValid section14Catalog 1 (⟨222,(13),[1,2,6,13,14],[170],744⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨744,[1,2,3,6,7,10,11,13,14,15],745⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3508 : RecordDataValid section14Catalog 1 (⟨222,(14),[1,2,5,6,13,14],[170],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3509 : RecordDataValid section14Catalog 1 (⟨222,(15),[1,2,5,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3510 : RecordDataValid section14Catalog 1 (⟨222,(16),[1,2,5,6,13,14],[170],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3511 : RecordDataValid section14Catalog 1 (⟨222,(17),[1,2,5,6,13,14],[170],745⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨745,[1,2,3,4,5,6,7,10,11,13,14,15,16],746⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3512 : RecordDataValid section14Catalog 1 (⟨222,(18),[1,2,5,6,13,14],[170],746⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨746,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],747⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3513 : RecordDataValid section14Catalog 1 (⟨222,(19),[1,2,5,6,13,14],[170],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3514 : RecordDataValid section14Catalog 1 (⟨222,(20),[1,2,5,6,13,14],[170],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3515 : RecordDataValid section14Catalog 1 (⟨222,(21),[1,2,5,6,13,14],[170],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3516 : RecordDataValid section14Catalog 1 (⟨222,(22),[1,2,5,6,13,14],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3517 : RecordDataValid section14Catalog 1 (⟨222,(23),[1,2,5,6,13,14],[170],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3518 : RecordDataValid section14Catalog 1 (⟨222,(24),[1,2,5,6,13,14],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3519 : RecordDataValid section14Catalog 1 (⟨224,(0),[1,2,5,6,13,14],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3488_3520 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3488).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3488).take 32 = [⟨221,(19),[1,2,5,6,13,14],[170],521⟩,⟨221,(20),[1,2,5,6,13,14],[170],522⟩,⟨221,(21),[1,2,5,6,13,14],[170],522⟩,⟨221,(22),[1,2,5,6,13,14],[170],522⟩,⟨221,(23),[1,2,5,6,13,14],[170],517⟩,⟨221,(24),[1,2,5,6,13,14],[170],518⟩,⟨222,(0),[1,2,6,13,14],[170],735⟩,⟨222,(1),[1,2,5,6,13,14],[170],736⟩,⟨222,(2),[1,2,5,6,13,14],[170],737⟩,⟨222,(3),[1,2,5,6,13,14],[170],736⟩,⟨222,(4),[1,2,5,6,13,14],[170],525⟩,⟨222,(5),[1,2,5,6,13,14],[170],735⟩,⟨222,(6),[1,2,6,13,14],[170],738⟩,⟨222,(7),[1,2,5,6,13,14],[170],739⟩,⟨222,(8),[1,2,5,6,13,14],[170],740⟩,⟨222,(9),[1,2,5,6,13,14],[170],528⟩,⟨222,(10),[1,2,6,13,14],[170],741⟩,⟨222,(11),[1,2,6,13,14],[170],742⟩,⟨222,(12),[1,2,6,13,14],[170],743⟩,⟨222,(13),[1,2,6,13,14],[170],744⟩,⟨222,(14),[1,2,5,6,13,14],[170],531⟩,⟨222,(15),[1,2,5,6,13,14],[170],735⟩,⟨222,(16),[1,2,5,6,13,14],[170],738⟩,⟨222,(17),[1,2,5,6,13,14],[170],745⟩,⟨222,(18),[1,2,5,6,13,14],[170],746⟩,⟨222,(19),[1,2,5,6,13,14],[170],534⟩,⟨222,(20),[1,2,5,6,13,14],[170],535⟩,⟨222,(21),[1,2,5,6,13,14],[170],536⟩,⟨222,(22),[1,2,5,6,13,14],[170],537⟩,⟨222,(23),[1,2,5,6,13,14],[170],538⟩,⟨222,(24),[1,2,5,6,13,14],[170],537⟩,⟨224,(0),[1,2,5,6,13,14],[170],539⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3488
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3489
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3490
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3491
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3492
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3493
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3494
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3495
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3496
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3497
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3498
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3499
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3500
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3501
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3502
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3503
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3504
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3505
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3506
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3507
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3508
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3509
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3510
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3511
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3512
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3513
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3514
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3515
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3516
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3517
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3518
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3519
end Section14Records_1_3488_3520

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3488_3520

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3456).take 64, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 3456 3488 3520 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_3456_3488 hnum) (Freiman.workReverse20260919_s0001_records_3488_3520 hnum))

#print axioms solution
