-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_2560_2688
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:53:52.781718+00:00
-- url     : https://prove2.me/submissions/6c202920-717a-4f44-ae04-065dbaae281c

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2560_2592
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2560_2592
private theorem valid2560 : RecordDataValid section14Catalog 1 (⟨111,(2),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2561 : RecordDataValid section14Catalog 1 (⟨111,(3),[1,5,6,13],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2562 : RecordDataValid section14Catalog 1 (⟨111,(4),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2563 : RecordDataValid section14Catalog 1 (⟨111,(5),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2564 : RecordDataValid section14Catalog 1 (⟨111,(6),[1,5,6,13],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2565 : RecordDataValid section14Catalog 1 (⟨111,(7),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2566 : RecordDataValid section14Catalog 1 (⟨111,(8),[1,5,6,13],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2567 : RecordDataValid section14Catalog 1 (⟨111,(9),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2568 : RecordDataValid section14Catalog 1 (⟨111,(10),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2569 : RecordDataValid section14Catalog 1 (⟨111,(11),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2570 : RecordDataValid section14Catalog 1 (⟨111,(12),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2571 : RecordDataValid section14Catalog 1 (⟨111,(13),[1,5,6,13],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2572 : RecordDataValid section14Catalog 1 (⟨111,(14),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2573 : RecordDataValid section14Catalog 1 (⟨111,(15),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2574 : RecordDataValid section14Catalog 1 (⟨111,(16),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2575 : RecordDataValid section14Catalog 1 (⟨111,(17),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2576 : RecordDataValid section14Catalog 1 (⟨111,(18),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2577 : RecordDataValid section14Catalog 1 (⟨111,(19),[1,5,6,13],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2578 : RecordDataValid section14Catalog 1 (⟨111,(20),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2579 : RecordDataValid section14Catalog 1 (⟨111,(21),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2580 : RecordDataValid section14Catalog 1 (⟨111,(22),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2581 : RecordDataValid section14Catalog 1 (⟨111,(23),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2582 : RecordDataValid section14Catalog 1 (⟨111,(24),[1,5,6,13],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2583 : RecordDataValid section14Catalog 1 (⟨114,(0),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2584 : RecordDataValid section14Catalog 1 (⟨114,(1),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2585 : RecordDataValid section14Catalog 1 (⟨114,(2),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2586 : RecordDataValid section14Catalog 1 (⟨114,(3),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2587 : RecordDataValid section14Catalog 1 (⟨114,(4),[1,5,6,13],[170],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2588 : RecordDataValid section14Catalog 1 (⟨114,(5),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2589 : RecordDataValid section14Catalog 1 (⟨114,(6),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2590 : RecordDataValid section14Catalog 1 (⟨114,(7),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2591 : RecordDataValid section14Catalog 1 (⟨114,(8),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2560_2592 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2560).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2560).take 32 = [⟨111,(2),[1,5,6,13],[170],453⟩,⟨111,(3),[1,5,6,13],[170],455⟩,⟨111,(4),[1,5,6,13],[170],456⟩,⟨111,(5),[1,5,6,13],[170],453⟩,⟨111,(6),[1,5,6,13],[170],454⟩,⟨111,(7),[1,5,6,13],[170],453⟩,⟨111,(8),[1,5,6,13],[170],455⟩,⟨111,(9),[1,5,6,13],[170],456⟩,⟨111,(10),[1,5,6,13],[170],457⟩,⟨111,(11),[1,5,6,13],[170],457⟩,⟨111,(12),[1,5,6,13],[170],457⟩,⟨111,(13),[1,5,6,13],[170],457⟩,⟨111,(14),[1,5,6,13],[170],456⟩,⟨111,(15),[1,5,6,13],[170],458⟩,⟨111,(16),[1,5,6,13],[170],458⟩,⟨111,(17),[1,5,6,13],[170],458⟩,⟨111,(18),[1,5,6,13],[170],458⟩,⟨111,(19),[1,5,6,13],[170],458⟩,⟨111,(20),[1,5,6,13],[170],459⟩,⟨111,(21),[1,5,6,13],[170],459⟩,⟨111,(22),[1,5,6,13],[170],459⟩,⟨111,(23),[1,5,6,13],[170],459⟩,⟨111,(24),[1,5,6,13],[170],459⟩,⟨114,(0),[1,5,6,13],[170],460⟩,⟨114,(1),[1,5,6,13],[170],460⟩,⟨114,(2),[1,5,6,13],[170],460⟩,⟨114,(3),[1,5,6,13],[170],460⟩,⟨114,(4),[1,5,6,13],[170],460⟩,⟨114,(5),[1,5,6,13],[170],461⟩,⟨114,(6),[1,5,6,13],[170],461⟩,⟨114,(7),[1,5,6,13],[170],461⟩,⟨114,(8),[1,5,6,13],[170],461⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2560
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2561
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2562
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2563
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2564
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2565
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2566
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2567
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2568
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2569
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2570
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2571
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2572
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2573
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2574
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2575
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2576
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2577
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2578
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2579
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2580
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2581
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2582
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2583
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2584
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2585
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2586
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2587
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2588
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2589
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2590
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2591
end Section14Records_1_2560_2592

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2560_2592


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2592_2624
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2592_2624
private theorem valid2592 : RecordDataValid section14Catalog 1 (⟨114,(9),[1,5,6,13],[170],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2593 : RecordDataValid section14Catalog 1 (⟨114,(10),[1,5,6,13],[170],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2594 : RecordDataValid section14Catalog 1 (⟨114,(11),[1,5,6,13],[170],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2595 : RecordDataValid section14Catalog 1 (⟨114,(12),[1,5,6,13],[170],464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨464,[1,4,5,6,8,9,10,12,13,16],465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2596 : RecordDataValid section14Catalog 1 (⟨114,(13),[1,5,6,13],[170],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2597 : RecordDataValid section14Catalog 1 (⟨114,(14),[1,5,6,13],[170],465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨465,[1,4,5,6,8,9,10,12,13,16],466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2598 : RecordDataValid section14Catalog 1 (⟨114,(15),[1,5,6,13],[170],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2599 : RecordDataValid section14Catalog 1 (⟨114,(16),[1,5,6,13],[170],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2600 : RecordDataValid section14Catalog 1 (⟨114,(17),[1,5,6,13],[170],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2601 : RecordDataValid section14Catalog 1 (⟨114,(18),[1,5,6,13],[170],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2602 : RecordDataValid section14Catalog 1 (⟨114,(19),[1,5,6,13],[170],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2603 : RecordDataValid section14Catalog 1 (⟨114,(20),[1,5,6,13],[170],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2604 : RecordDataValid section14Catalog 1 (⟨114,(21),[1,5,6,13],[170],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2605 : RecordDataValid section14Catalog 1 (⟨114,(22),[1,5,6,13],[170],464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨464,[1,4,5,6,8,9,10,12,13,16],465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2606 : RecordDataValid section14Catalog 1 (⟨114,(23),[1,5,6,13],[170],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2607 : RecordDataValid section14Catalog 1 (⟨114,(24),[1,5,6,13],[170],465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨465,[1,4,5,6,8,9,10,12,13,16],466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2608 : RecordDataValid section14Catalog 1 (⟨116,(0),[1,5,6,13],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2609 : RecordDataValid section14Catalog 1 (⟨116,(1),[1,5,6,13],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2610 : RecordDataValid section14Catalog 1 (⟨116,(2),[1,5,6,13],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2611 : RecordDataValid section14Catalog 1 (⟨116,(3),[1,5,6,13],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2612 : RecordDataValid section14Catalog 1 (⟨116,(4),[1,5,6,13],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2613 : RecordDataValid section14Catalog 1 (⟨116,(5),[1,5,6,13],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2614 : RecordDataValid section14Catalog 1 (⟨116,(6),[1,5,6,13],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2615 : RecordDataValid section14Catalog 1 (⟨116,(7),[1,5,6,13],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2616 : RecordDataValid section14Catalog 1 (⟨116,(8),[1,5,6,13],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2617 : RecordDataValid section14Catalog 1 (⟨116,(9),[1,5,6,13],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2618 : RecordDataValid section14Catalog 1 (⟨116,(10),[1,5,6,13],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2619 : RecordDataValid section14Catalog 1 (⟨116,(11),[1,5,6,13],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2620 : RecordDataValid section14Catalog 1 (⟨116,(12),[1,5,6,13],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2621 : RecordDataValid section14Catalog 1 (⟨116,(13),[1,5,6,13],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2622 : RecordDataValid section14Catalog 1 (⟨116,(14),[1,5,6,13],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2623 : RecordDataValid section14Catalog 1 (⟨116,(15),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2592_2624 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2592).take 32 = [⟨114,(9),[1,5,6,13],[170],461⟩,⟨114,(10),[1,5,6,13],[170],462⟩,⟨114,(11),[1,5,6,13],[170],463⟩,⟨114,(12),[1,5,6,13],[170],464⟩,⟨114,(13),[1,5,6,13],[170],463⟩,⟨114,(14),[1,5,6,13],[170],465⟩,⟨114,(15),[1,5,6,13],[170],462⟩,⟨114,(16),[1,5,6,13],[170],466⟩,⟨114,(17),[1,5,6,13],[170],466⟩,⟨114,(18),[1,5,6,13],[170],466⟩,⟨114,(19),[1,5,6,13],[170],466⟩,⟨114,(20),[1,5,6,13],[170],462⟩,⟨114,(21),[1,5,6,13],[170],463⟩,⟨114,(22),[1,5,6,13],[170],464⟩,⟨114,(23),[1,5,6,13],[170],463⟩,⟨114,(24),[1,5,6,13],[170],465⟩,⟨116,(0),[1,5,6,13],[170],467⟩,⟨116,(1),[1,5,6,13],[170],468⟩,⟨116,(2),[1,5,6,13],[170],467⟩,⟨116,(3),[1,5,6,13],[170],469⟩,⟨116,(4),[1,5,6,13],[170],470⟩,⟨116,(5),[1,5,6,13],[170],467⟩,⟨116,(6),[1,5,6,13],[170],468⟩,⟨116,(7),[1,5,6,13],[170],467⟩,⟨116,(8),[1,5,6,13],[170],469⟩,⟨116,(9),[1,5,6,13],[170],470⟩,⟨116,(10),[1,5,6,13],[170],471⟩,⟨116,(11),[1,5,6,13],[170],471⟩,⟨116,(12),[1,5,6,13],[170],471⟩,⟨116,(13),[1,5,6,13],[170],471⟩,⟨116,(14),[1,5,6,13],[170],470⟩,⟨116,(15),[1,5,6,13],[170],472⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2592
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2593
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2594
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2595
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2596
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2597
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2598
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2599
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2600
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2601
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2602
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2603
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2604
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2605
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2606
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2607
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2608
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2609
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2610
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2611
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2612
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2613
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2614
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2615
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2616
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2617
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2618
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2619
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2620
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2621
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2622
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2623
end Section14Records_1_2592_2624

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2592_2624


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2624_2656
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2624_2656
private theorem valid2624 : RecordDataValid section14Catalog 1 (⟨116,(16),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2625 : RecordDataValid section14Catalog 1 (⟨116,(17),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2626 : RecordDataValid section14Catalog 1 (⟨116,(18),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2627 : RecordDataValid section14Catalog 1 (⟨116,(19),[1,5,6,13],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2628 : RecordDataValid section14Catalog 1 (⟨116,(20),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2629 : RecordDataValid section14Catalog 1 (⟨116,(21),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2630 : RecordDataValid section14Catalog 1 (⟨116,(22),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2631 : RecordDataValid section14Catalog 1 (⟨116,(23),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2632 : RecordDataValid section14Catalog 1 (⟨116,(24),[1,5,6,13],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2633 : RecordDataValid section14Catalog 1 (⟨119,(0),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2634 : RecordDataValid section14Catalog 1 (⟨119,(1),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2635 : RecordDataValid section14Catalog 1 (⟨119,(2),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2636 : RecordDataValid section14Catalog 1 (⟨119,(3),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2637 : RecordDataValid section14Catalog 1 (⟨119,(4),[1,5,6,13],[170],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2638 : RecordDataValid section14Catalog 1 (⟨119,(5),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2639 : RecordDataValid section14Catalog 1 (⟨119,(6),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2640 : RecordDataValid section14Catalog 1 (⟨119,(7),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2641 : RecordDataValid section14Catalog 1 (⟨119,(8),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2642 : RecordDataValid section14Catalog 1 (⟨119,(9),[1,5,6,13],[170],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2643 : RecordDataValid section14Catalog 1 (⟨119,(10),[1,5,6,13],[170],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2644 : RecordDataValid section14Catalog 1 (⟨119,(11),[1,5,6,13],[170],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2645 : RecordDataValid section14Catalog 1 (⟨119,(12),[1,5,6,13],[170],478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨478,[1,4,5,6,8,9,10,12,13,16],479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2646 : RecordDataValid section14Catalog 1 (⟨119,(13),[1,5,6,13],[170],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2647 : RecordDataValid section14Catalog 1 (⟨119,(14),[1,5,6,13],[170],479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨479,[1,4,5,6,8,9,10,12,13,16],480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2648 : RecordDataValid section14Catalog 1 (⟨119,(15),[1,5,6,13],[170],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2649 : RecordDataValid section14Catalog 1 (⟨119,(16),[1,5,6,13],[170],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2650 : RecordDataValid section14Catalog 1 (⟨119,(17),[1,5,6,13],[170],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2651 : RecordDataValid section14Catalog 1 (⟨119,(18),[1,5,6,13],[170],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2652 : RecordDataValid section14Catalog 1 (⟨119,(19),[1,5,6,13],[170],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2653 : RecordDataValid section14Catalog 1 (⟨119,(20),[1,5,6,13],[170],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2654 : RecordDataValid section14Catalog 1 (⟨119,(21),[1,5,6,13],[170],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2655 : RecordDataValid section14Catalog 1 (⟨119,(22),[1,5,6,13],[170],478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨478,[1,4,5,6,8,9,10,12,13,16],479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2624_2656 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2624).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2624).take 32 = [⟨116,(16),[1,5,6,13],[170],472⟩,⟨116,(17),[1,5,6,13],[170],472⟩,⟨116,(18),[1,5,6,13],[170],472⟩,⟨116,(19),[1,5,6,13],[170],472⟩,⟨116,(20),[1,5,6,13],[170],473⟩,⟨116,(21),[1,5,6,13],[170],473⟩,⟨116,(22),[1,5,6,13],[170],473⟩,⟨116,(23),[1,5,6,13],[170],473⟩,⟨116,(24),[1,5,6,13],[170],473⟩,⟨119,(0),[1,5,6,13],[170],474⟩,⟨119,(1),[1,5,6,13],[170],474⟩,⟨119,(2),[1,5,6,13],[170],474⟩,⟨119,(3),[1,5,6,13],[170],474⟩,⟨119,(4),[1,5,6,13],[170],474⟩,⟨119,(5),[1,5,6,13],[170],475⟩,⟨119,(6),[1,5,6,13],[170],475⟩,⟨119,(7),[1,5,6,13],[170],475⟩,⟨119,(8),[1,5,6,13],[170],475⟩,⟨119,(9),[1,5,6,13],[170],475⟩,⟨119,(10),[1,5,6,13],[170],476⟩,⟨119,(11),[1,5,6,13],[170],477⟩,⟨119,(12),[1,5,6,13],[170],478⟩,⟨119,(13),[1,5,6,13],[170],477⟩,⟨119,(14),[1,5,6,13],[170],479⟩,⟨119,(15),[1,5,6,13],[170],476⟩,⟨119,(16),[1,5,6,13],[170],480⟩,⟨119,(17),[1,5,6,13],[170],480⟩,⟨119,(18),[1,5,6,13],[170],480⟩,⟨119,(19),[1,5,6,13],[170],480⟩,⟨119,(20),[1,5,6,13],[170],476⟩,⟨119,(21),[1,5,6,13],[170],477⟩,⟨119,(22),[1,5,6,13],[170],478⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2624
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2625
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2626
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2627
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2628
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2629
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2630
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2631
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2632
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2633
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2634
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2635
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2636
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2637
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2638
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2639
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2640
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2641
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2642
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2643
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2644
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2645
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2646
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2647
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2648
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2649
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2650
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2651
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2652
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2653
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2654
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2655
end Section14Records_1_2624_2656

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2624_2656


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2656_2688
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2656_2688
private theorem valid2656 : RecordDataValid section14Catalog 1 (⟨119,(23),[1,5,6,13],[170],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2657 : RecordDataValid section14Catalog 1 (⟨119,(24),[1,5,6,13],[170],479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨479,[1,4,5,6,8,9,10,12,13,16],480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2658 : RecordDataValid section14Catalog 1 (⟨121,(0),[1,5,6,13],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2659 : RecordDataValid section14Catalog 1 (⟨121,(1),[1,5,6,13],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2660 : RecordDataValid section14Catalog 1 (⟨121,(2),[1,5,6,13],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2661 : RecordDataValid section14Catalog 1 (⟨121,(3),[1,5,6,13],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2662 : RecordDataValid section14Catalog 1 (⟨121,(4),[1,5,6,13],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2663 : RecordDataValid section14Catalog 1 (⟨121,(5),[1,5,6,13],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2664 : RecordDataValid section14Catalog 1 (⟨121,(6),[1,5,6,13],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2665 : RecordDataValid section14Catalog 1 (⟨121,(7),[1,5,6,13],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2666 : RecordDataValid section14Catalog 1 (⟨121,(8),[1,5,6,13],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2667 : RecordDataValid section14Catalog 1 (⟨121,(9),[1,5,6,13],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2668 : RecordDataValid section14Catalog 1 (⟨121,(10),[1,5,6,13],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2669 : RecordDataValid section14Catalog 1 (⟨121,(11),[1,5,6,13],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2670 : RecordDataValid section14Catalog 1 (⟨121,(12),[1,5,6,13],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2671 : RecordDataValid section14Catalog 1 (⟨121,(13),[1,5,6,13],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2672 : RecordDataValid section14Catalog 1 (⟨121,(14),[1,5,6,13],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2673 : RecordDataValid section14Catalog 1 (⟨121,(15),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2674 : RecordDataValid section14Catalog 1 (⟨121,(16),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2675 : RecordDataValid section14Catalog 1 (⟨121,(17),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2676 : RecordDataValid section14Catalog 1 (⟨121,(18),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2677 : RecordDataValid section14Catalog 1 (⟨121,(19),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2678 : RecordDataValid section14Catalog 1 (⟨121,(20),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2679 : RecordDataValid section14Catalog 1 (⟨121,(21),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2680 : RecordDataValid section14Catalog 1 (⟨121,(22),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2681 : RecordDataValid section14Catalog 1 (⟨121,(23),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2682 : RecordDataValid section14Catalog 1 (⟨121,(24),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2683 : RecordDataValid section14Catalog 1 (⟨124,(0),[1,5,6,13],[170],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2684 : RecordDataValid section14Catalog 1 (⟨124,(1),[1,5,6,13],[170],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2685 : RecordDataValid section14Catalog 1 (⟨124,(2),[1,5,6,13],[170],490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨490,[1,4,5,6,8,9,10,12,13,16],491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2686 : RecordDataValid section14Catalog 1 (⟨124,(3),[1,5,6,13],[170],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2687 : RecordDataValid section14Catalog 1 (⟨124,(4),[1,5,6,13],[170],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2656_2688 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2656).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2656).take 32 = [⟨119,(23),[1,5,6,13],[170],477⟩,⟨119,(24),[1,5,6,13],[170],479⟩,⟨121,(0),[1,5,6,13],[170],481⟩,⟨121,(1),[1,5,6,13],[170],482⟩,⟨121,(2),[1,5,6,13],[170],481⟩,⟨121,(3),[1,5,6,13],[170],483⟩,⟨121,(4),[1,5,6,13],[170],484⟩,⟨121,(5),[1,5,6,13],[170],481⟩,⟨121,(6),[1,5,6,13],[170],482⟩,⟨121,(7),[1,5,6,13],[170],481⟩,⟨121,(8),[1,5,6,13],[170],483⟩,⟨121,(9),[1,5,6,13],[170],484⟩,⟨121,(10),[1,5,6,13],[170],485⟩,⟨121,(11),[1,5,6,13],[170],485⟩,⟨121,(12),[1,5,6,13],[170],485⟩,⟨121,(13),[1,5,6,13],[170],485⟩,⟨121,(14),[1,5,6,13],[170],484⟩,⟨121,(15),[1,5,6,13],[170],486⟩,⟨121,(16),[1,5,6,13],[170],486⟩,⟨121,(17),[1,5,6,13],[170],486⟩,⟨121,(18),[1,5,6,13],[170],486⟩,⟨121,(19),[1,5,6,13],[170],486⟩,⟨121,(20),[1,5,6,13],[170],487⟩,⟨121,(21),[1,5,6,13],[170],487⟩,⟨121,(22),[1,5,6,13],[170],487⟩,⟨121,(23),[1,5,6,13],[170],487⟩,⟨121,(24),[1,5,6,13],[170],487⟩,⟨124,(0),[1,5,6,13],[170],488⟩,⟨124,(1),[1,5,6,13],[170],489⟩,⟨124,(2),[1,5,6,13],[170],490⟩,⟨124,(3),[1,5,6,13],[170],491⟩,⟨124,(4),[1,5,6,13],[170],488⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2656
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2657
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2658
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2659
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2660
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2661
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2662
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2663
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2664
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2665
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2666
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2667
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2668
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2669
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2670
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2671
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2672
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2673
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2674
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2675
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2676
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2677
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2678
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2679
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2680
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2681
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2682
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2683
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2684
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2685
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2686
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2687
end Section14Records_1_2656_2688

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2656_2688

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2560).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 2560 2624 2688 (by decide) (by decide) (all_of_interval_split P xs 2560 2592 2624 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_2560_2592 hnum) (Freiman.workReverse20260919_s0001_records_2592_2624 hnum)) (all_of_interval_split P xs 2624 2656 2688 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_2624_2656 hnum) (Freiman.workReverse20260919_s0001_records_2656_2688 hnum)))

#print axioms solution
