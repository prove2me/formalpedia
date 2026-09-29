-- Prove2me | solution 1 for Freiman.section14_s0002_records_2592_2624
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:21:56.900981+00:00
-- url     : https://prove2.me/submissions/ce0b3092-09e7-4af9-a824-f5cbbbb99dc6

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
namespace Section14Records_2_2592_2624
private theorem valid2592 : RecordDataValid section14Catalog 2 (⟨253,(13),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2593 : RecordDataValid section14Catalog 2 (⟨253,(14),[1,2,5,6,13,14],[170],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2594 : RecordDataValid section14Catalog 2 (⟨253,(15),[1,2,5,6,13,14],[170],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2595 : RecordDataValid section14Catalog 2 (⟨253,(16),[1,2,5,6,13,14],[170],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2596 : RecordDataValid section14Catalog 2 (⟨253,(17),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2597 : RecordDataValid section14Catalog 2 (⟨253,(18),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2598 : RecordDataValid section14Catalog 2 (⟨253,(19),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2599 : RecordDataValid section14Catalog 2 (⟨253,(20),[1,2,5,6,13,14],[170],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2600 : RecordDataValid section14Catalog 2 (⟨253,(21),[1,2,5,6,13,14],[170],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2601 : RecordDataValid section14Catalog 2 (⟨253,(22),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2602 : RecordDataValid section14Catalog 2 (⟨253,(23),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2603 : RecordDataValid section14Catalog 2 (⟨253,(24),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2604 : RecordDataValid section14Catalog 2 (⟨255,(0),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2605 : RecordDataValid section14Catalog 2 (⟨255,(1),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2606 : RecordDataValid section14Catalog 2 (⟨255,(2),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2607 : RecordDataValid section14Catalog 2 (⟨255,(3),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2608 : RecordDataValid section14Catalog 2 (⟨255,(4),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2609 : RecordDataValid section14Catalog 2 (⟨255,(5),[1,2,5,6],[170],903⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨903,[1,2,4,5,6,8],905⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2610 : RecordDataValid section14Catalog 2 (⟨255,(6),[1,2,5,6],[170],903⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨903,[1,2,4,5,6,8],905⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2611 : RecordDataValid section14Catalog 2 (⟨255,(7),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2612 : RecordDataValid section14Catalog 2 (⟨255,(8),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2613 : RecordDataValid section14Catalog 2 (⟨255,(9),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2614 : RecordDataValid section14Catalog 2 (⟨255,(10),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2615 : RecordDataValid section14Catalog 2 (⟨255,(11),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2616 : RecordDataValid section14Catalog 2 (⟨255,(12),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2617 : RecordDataValid section14Catalog 2 (⟨255,(13),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2618 : RecordDataValid section14Catalog 2 (⟨255,(14),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2619 : RecordDataValid section14Catalog 2 (⟨255,(15),[1,2,5,6],[170],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2620 : RecordDataValid section14Catalog 2 (⟨255,(16),[1,2,5,6],[170],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2621 : RecordDataValid section14Catalog 2 (⟨255,(17),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2622 : RecordDataValid section14Catalog 2 (⟨255,(18),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2623 : RecordDataValid section14Catalog 2 (⟨255,(19),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2592).take 32 = [⟨253,(13),[1,2,5,6,13,14],[170],29⟩,⟨253,(14),[1,2,5,6,13,14],[170],34⟩,⟨253,(15),[1,2,5,6,13,14],[170],35⟩,⟨253,(16),[1,2,5,6,13,14],[170],36⟩,⟨253,(17),[1,2,5,6,13,14],[170],37⟩,⟨253,(18),[1,2,5,6,13,14],[170],29⟩,⟨253,(19),[1,2,5,6,13,14],[170],37⟩,⟨253,(20),[1,2,5,6,13,14],[170],38⟩,⟨253,(21),[1,2,5,6,13,14],[170],39⟩,⟨253,(22),[1,2,5,6,13,14],[170],40⟩,⟨253,(23),[1,2,5,6,13,14],[170],29⟩,⟨253,(24),[1,2,5,6,13,14],[170],40⟩,⟨255,(0),[1,2,5,6],[170],899⟩,⟨255,(1),[1,2,5,6],[170],899⟩,⟨255,(2),[1,2,5,6],[170],900⟩,⟨255,(3),[1,2,5,6],[170],901⟩,⟨255,(4),[1,2,5,6],[170],902⟩,⟨255,(5),[1,2,5,6],[170],903⟩,⟨255,(6),[1,2,5,6],[170],903⟩,⟨255,(7),[1,2,5,6],[170],900⟩,⟨255,(8),[1,2,5,6],[170],901⟩,⟨255,(9),[1,2,5,6],[170],902⟩,⟨255,(10),[1,2,5,6],[170],899⟩,⟨255,(11),[1,2,5,6],[170],899⟩,⟨255,(12),[1,2,5,6],[170],900⟩,⟨255,(13),[1,2,5,6],[170],901⟩,⟨255,(14),[1,2,5,6],[170],902⟩,⟨255,(15),[1,2,5,6],[170],904⟩,⟨255,(16),[1,2,5,6],[170],904⟩,⟨255,(17),[1,2,5,6],[170],900⟩,⟨255,(18),[1,2,5,6],[170],901⟩,⟨255,(19),[1,2,5,6],[170],902⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2592
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2593
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2594
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2595
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2596
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2597
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2598
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2599
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2600
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2601
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2602
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2603
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2604
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2605
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2606
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2607
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2608
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2609
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2610
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2611
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2612
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2613
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2614
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2615
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2616
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2617
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2618
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2619
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2620
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2621
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2622
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2623
end Section14Records_2_2592_2624

#print axioms solution
