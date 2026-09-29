-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2624_2688
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:16:20.700154+00:00
-- url     : https://prove2.me/submissions/251d5642-02f4-4760-918e-c5de905bd279

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2624_2656
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2624_2656
private theorem valid2624 : RecordDataValid section14Catalog 6 (⟨185,(8),[5,6],[174],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2625 : RecordDataValid section14Catalog 6 (⟨185,(9),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2626 : RecordDataValid section14Catalog 6 (⟨185,(9),[5,6],[174],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2627 : RecordDataValid section14Catalog 6 (⟨185,(10),[1,2,5,6,13,14],[170],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2628 : RecordDataValid section14Catalog 6 (⟨185,(10),[5,6],[174],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2629 : RecordDataValid section14Catalog 6 (⟨185,(11),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2630 : RecordDataValid section14Catalog 6 (⟨185,(11),[5,6],[174],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2631 : RecordDataValid section14Catalog 6 (⟨185,(12),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2632 : RecordDataValid section14Catalog 6 (⟨185,(12),[5,6],[174],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2633 : RecordDataValid section14Catalog 6 (⟨185,(13),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2634 : RecordDataValid section14Catalog 6 (⟨185,(13),[5,6],[174],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2635 : RecordDataValid section14Catalog 6 (⟨185,(14),[1,2,5,6,13,14],[170],683⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨683,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],684⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2636 : RecordDataValid section14Catalog 6 (⟨185,(14),[5,6],[174],683⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨683,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],684⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2637 : RecordDataValid section14Catalog 6 (⟨185,(15),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2638 : RecordDataValid section14Catalog 6 (⟨185,(15),[5,6],[174],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2639 : RecordDataValid section14Catalog 6 (⟨188,(0),[1,2,5,6,13,14],[170],684⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨684,[1,2,3,5,6,7,10,11,13,14,15],685⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2640 : RecordDataValid section14Catalog 6 (⟨188,(0),[5,6],[174],995⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨995,[3,5,6,7],999⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2641 : RecordDataValid section14Catalog 6 (⟨188,(1),[1,2,5,6,13,14],[170],685⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨685,[1,2,3,5,6,7,10,11,13,14,15],686⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2642 : RecordDataValid section14Catalog 6 (⟨188,(1),[5,6],[174],996⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨996,[3,5,6,7],1000⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2643 : RecordDataValid section14Catalog 6 (⟨188,(2),[1,2,5,6,13,14],[170],684⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨684,[1,2,3,5,6,7,10,11,13,14,15],685⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2644 : RecordDataValid section14Catalog 6 (⟨188,(2),[5,6],[174],995⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨995,[3,5,6,7],999⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2645 : RecordDataValid section14Catalog 6 (⟨188,(3),[1,2,5,6,13,14],[170],686⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨686,[1,2,3,5,6,7,10,11,13,14,15],687⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2646 : RecordDataValid section14Catalog 6 (⟨188,(3),[5,6],[174],997⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨997,[3,5,6,7],1001⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2647 : RecordDataValid section14Catalog 6 (⟨188,(4),[1,2,5,6,13,14],[170],687⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨687,[1,2,3,5,6,7,10,11,13,14,15],688⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2648 : RecordDataValid section14Catalog 6 (⟨188,(4),[5,6],[174],998⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨998,[3,5,6,7],1002⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2649 : RecordDataValid section14Catalog 6 (⟨188,(5),[1,2,5,6,13,14],[170],687⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨687,[1,2,3,5,6,7,10,11,13,14,15],688⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2650 : RecordDataValid section14Catalog 6 (⟨188,(5),[5,6],[174],998⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨998,[3,5,6,7],1002⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2651 : RecordDataValid section14Catalog 6 (⟨188,(6),[1,2,5,6,13,14],[170],687⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨687,[1,2,3,5,6,7,10,11,13,14,15],688⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2652 : RecordDataValid section14Catalog 6 (⟨188,(6),[5,6],[174],998⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨998,[3,5,6,7],1002⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2653 : RecordDataValid section14Catalog 6 (⟨188,(7),[1,2,5,6,13,14],[170],687⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨687,[1,2,3,5,6,7,10,11,13,14,15],688⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2654 : RecordDataValid section14Catalog 6 (⟨188,(7),[5,6],[174],998⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨998,[3,5,6,7],1002⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2655 : RecordDataValid section14Catalog 6 (⟨188,(8),[1,2,5,6,13,14],[170],688⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨688,[1,2,3,5,6,7,10,11,13,14,15],689⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2624_2656 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2624).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2624).take 32 = [⟨185,(8),[5,6],[174],678⟩,⟨185,(9),[1,2,5,6,13,14],[170],679⟩,⟨185,(9),[5,6],[174],679⟩,⟨185,(10),[1,2,5,6,13,14],[170],680⟩,⟨185,(10),[5,6],[174],680⟩,⟨185,(11),[1,2,5,6,13,14],[170],681⟩,⟨185,(11),[5,6],[174],681⟩,⟨185,(12),[1,2,5,6,13,14],[170],678⟩,⟨185,(12),[5,6],[174],678⟩,⟨185,(13),[1,2,5,6,13,14],[170],679⟩,⟨185,(13),[5,6],[174],679⟩,⟨185,(14),[1,2,5,6,13,14],[170],683⟩,⟨185,(14),[5,6],[174],683⟩,⟨185,(15),[1,2,5,6,13,14],[170],681⟩,⟨185,(15),[5,6],[174],681⟩,⟨188,(0),[1,2,5,6,13,14],[170],684⟩,⟨188,(0),[5,6],[174],995⟩,⟨188,(1),[1,2,5,6,13,14],[170],685⟩,⟨188,(1),[5,6],[174],996⟩,⟨188,(2),[1,2,5,6,13,14],[170],684⟩,⟨188,(2),[5,6],[174],995⟩,⟨188,(3),[1,2,5,6,13,14],[170],686⟩,⟨188,(3),[5,6],[174],997⟩,⟨188,(4),[1,2,5,6,13,14],[170],687⟩,⟨188,(4),[5,6],[174],998⟩,⟨188,(5),[1,2,5,6,13,14],[170],687⟩,⟨188,(5),[5,6],[174],998⟩,⟨188,(6),[1,2,5,6,13,14],[170],687⟩,⟨188,(6),[5,6],[174],998⟩,⟨188,(7),[1,2,5,6,13,14],[170],687⟩,⟨188,(7),[5,6],[174],998⟩,⟨188,(8),[1,2,5,6,13,14],[170],688⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2624
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2625
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2626
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2627
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2628
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2629
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2630
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2631
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2632
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2633
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2634
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2635
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2636
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2637
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2638
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2639
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2640
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2641
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2642
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2643
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2644
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2645
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2646
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2647
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2648
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2649
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2650
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2651
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2652
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2653
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2654
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2655
end Section14Records_6_2624_2656

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2624_2656


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2656_2688
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2656_2688
private theorem valid2656 : RecordDataValid section14Catalog 6 (⟨188,(8),[5,6],[174],999⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨999,[3,5,6,7],1003⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2657 : RecordDataValid section14Catalog 6 (⟨188,(9),[1,2,5,6,13,14],[170],688⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨688,[1,2,3,5,6,7,10,11,13,14,15],689⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2658 : RecordDataValid section14Catalog 6 (⟨188,(9),[5,6],[174],999⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨999,[3,5,6,7],1003⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2659 : RecordDataValid section14Catalog 6 (⟨188,(10),[1,2,5,6,13,14],[170],688⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨688,[1,2,3,5,6,7,10,11,13,14,15],689⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2660 : RecordDataValid section14Catalog 6 (⟨188,(10),[5,6],[174],999⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨999,[3,5,6,7],1003⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2661 : RecordDataValid section14Catalog 6 (⟨188,(11),[1,2,5,6,13,14],[170],688⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨688,[1,2,3,5,6,7,10,11,13,14,15],689⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2662 : RecordDataValid section14Catalog 6 (⟨188,(11),[5,6],[174],999⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨999,[3,5,6,7],1003⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2663 : RecordDataValid section14Catalog 6 (⟨188,(12),[1,2,5,6,13,14],[170],689⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨689,[1,2,3,5,6,7,10,11,13,14,15],690⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2664 : RecordDataValid section14Catalog 6 (⟨188,(12),[5,6],[174],1000⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1000,[3,5,6,7],1004⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2665 : RecordDataValid section14Catalog 6 (⟨188,(13),[1,2,5,6,13,14],[170],689⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨689,[1,2,3,5,6,7,10,11,13,14,15],690⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2666 : RecordDataValid section14Catalog 6 (⟨188,(13),[5,6],[174],1000⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1000,[3,5,6,7],1004⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2667 : RecordDataValid section14Catalog 6 (⟨188,(14),[1,2,5,6,13,14],[170],689⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨689,[1,2,3,5,6,7,10,11,13,14,15],690⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2668 : RecordDataValid section14Catalog 6 (⟨188,(14),[5,6],[174],1000⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1000,[3,5,6,7],1004⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2669 : RecordDataValid section14Catalog 6 (⟨188,(15),[1,2,5,6,13,14],[170],689⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨689,[1,2,3,5,6,7,10,11,13,14,15],690⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2670 : RecordDataValid section14Catalog 6 (⟨188,(15),[5,6],[174],1000⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1000,[3,5,6,7],1004⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2671 : RecordDataValid section14Catalog 6 (⟨190,(0),[1,2,5,6,13,14],[170],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2672 : RecordDataValid section14Catalog 6 (⟨190,(0),[5,6],[174],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2673 : RecordDataValid section14Catalog 6 (⟨190,(1),[1,2,5,6,13,14],[170],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2674 : RecordDataValid section14Catalog 6 (⟨190,(1),[5,6],[174],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2675 : RecordDataValid section14Catalog 6 (⟨190,(2),[1,2,5,6,13,14],[170],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2676 : RecordDataValid section14Catalog 6 (⟨190,(2),[5,6],[174],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2677 : RecordDataValid section14Catalog 6 (⟨190,(3),[1,2,5,6,13,14],[170],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2678 : RecordDataValid section14Catalog 6 (⟨190,(3),[5,6],[174],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2679 : RecordDataValid section14Catalog 6 (⟨190,(4),[1,2,5,6,13,14],[170],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2680 : RecordDataValid section14Catalog 6 (⟨190,(4),[5,6],[174],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2681 : RecordDataValid section14Catalog 6 (⟨190,(5),[1,2,5,6,13,14],[170],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2682 : RecordDataValid section14Catalog 6 (⟨190,(5),[5,6],[174],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2683 : RecordDataValid section14Catalog 6 (⟨190,(6),[1,2,5,6,13,14],[170],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2684 : RecordDataValid section14Catalog 6 (⟨190,(6),[5,6],[174],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2685 : RecordDataValid section14Catalog 6 (⟨190,(7),[1,2,5,6,13,14],[170],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2686 : RecordDataValid section14Catalog 6 (⟨190,(7),[5,6],[174],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2687 : RecordDataValid section14Catalog 6 (⟨190,(8),[1,2,5,6,13,14],[170],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2656_2688 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2656).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2656).take 32 = [⟨188,(8),[5,6],[174],999⟩,⟨188,(9),[1,2,5,6,13,14],[170],688⟩,⟨188,(9),[5,6],[174],999⟩,⟨188,(10),[1,2,5,6,13,14],[170],688⟩,⟨188,(10),[5,6],[174],999⟩,⟨188,(11),[1,2,5,6,13,14],[170],688⟩,⟨188,(11),[5,6],[174],999⟩,⟨188,(12),[1,2,5,6,13,14],[170],689⟩,⟨188,(12),[5,6],[174],1000⟩,⟨188,(13),[1,2,5,6,13,14],[170],689⟩,⟨188,(13),[5,6],[174],1000⟩,⟨188,(14),[1,2,5,6,13,14],[170],689⟩,⟨188,(14),[5,6],[174],1000⟩,⟨188,(15),[1,2,5,6,13,14],[170],689⟩,⟨188,(15),[5,6],[174],1000⟩,⟨190,(0),[1,2,5,6,13,14],[170],690⟩,⟨190,(0),[5,6],[174],690⟩,⟨190,(1),[1,2,5,6,13,14],[170],690⟩,⟨190,(1),[5,6],[174],690⟩,⟨190,(2),[1,2,5,6,13,14],[170],690⟩,⟨190,(2),[5,6],[174],690⟩,⟨190,(3),[1,2,5,6,13,14],[170],690⟩,⟨190,(3),[5,6],[174],690⟩,⟨190,(4),[1,2,5,6,13,14],[170],690⟩,⟨190,(4),[5,6],[174],690⟩,⟨190,(5),[1,2,5,6,13,14],[170],691⟩,⟨190,(5),[5,6],[174],691⟩,⟨190,(6),[1,2,5,6,13,14],[170],691⟩,⟨190,(6),[5,6],[174],691⟩,⟨190,(7),[1,2,5,6,13,14],[170],691⟩,⟨190,(7),[5,6],[174],691⟩,⟨190,(8),[1,2,5,6,13,14],[170],691⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2656
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2657
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2658
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2659
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2660
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2661
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2662
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2663
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2664
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2665
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2666
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2667
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2668
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2669
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2670
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2671
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2672
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2673
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2674
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2675
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2676
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2677
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2678
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2679
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2680
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2681
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2682
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2683
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2684
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2685
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2686
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2687
end Section14Records_6_2656_2688

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2656_2688

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2624).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2624 2656 2688 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2624_2656 hnum) (Freiman.workReverse20260919_s0006_records_2656_2688 hnum))

#print axioms solution
