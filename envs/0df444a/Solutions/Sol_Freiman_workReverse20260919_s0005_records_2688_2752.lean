-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_2688_2752
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:27:43.189998+00:00
-- url     : https://prove2.me/submissions/f2332e51-8a94-4561-b060-b84ea9b1daab

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2688_2720
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2688_2720
private theorem valid2688 : RecordDataValid section14Catalog 5 (⟨166,(11),[1,2,5,6,13,14],[170],648⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨648,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],649⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2689 : RecordDataValid section14Catalog 5 (⟨166,(11),[5,6],[174],648⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨648,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],649⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2690 : RecordDataValid section14Catalog 5 (⟨166,(12),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2691 : RecordDataValid section14Catalog 5 (⟨166,(12),[5,6],[174],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2692 : RecordDataValid section14Catalog 5 (⟨166,(13),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2693 : RecordDataValid section14Catalog 5 (⟨166,(13),[5,6],[174],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2694 : RecordDataValid section14Catalog 5 (⟨166,(14),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2695 : RecordDataValid section14Catalog 5 (⟨166,(14),[5,6],[174],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2696 : RecordDataValid section14Catalog 5 (⟨166,(15),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2697 : RecordDataValid section14Catalog 5 (⟨166,(15),[5,6],[174],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2698 : RecordDataValid section14Catalog 5 (⟨167,(0),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2699 : RecordDataValid section14Catalog 5 (⟨167,(0),[5,6],[174],971⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨971,[3,5,6,7],975⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2700 : RecordDataValid section14Catalog 5 (⟨167,(1),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2701 : RecordDataValid section14Catalog 5 (⟨167,(1),[5,6],[174],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2702 : RecordDataValid section14Catalog 5 (⟨167,(2),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2703 : RecordDataValid section14Catalog 5 (⟨167,(2),[5,6],[174],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2704 : RecordDataValid section14Catalog 5 (⟨167,(3),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2705 : RecordDataValid section14Catalog 5 (⟨167,(3),[5,6],[174],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2706 : RecordDataValid section14Catalog 5 (⟨167,(4),[1,2,5,6,13,14],[170],422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2707 : RecordDataValid section14Catalog 5 (⟨167,(4),[5,6],[174],975⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨975,[3,5,6,7],979⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2708 : RecordDataValid section14Catalog 5 (⟨167,(5),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2709 : RecordDataValid section14Catalog 5 (⟨167,(5),[5,6],[174],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2710 : RecordDataValid section14Catalog 5 (⟨167,(6),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2711 : RecordDataValid section14Catalog 5 (⟨167,(6),[5,6],[174],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2712 : RecordDataValid section14Catalog 5 (⟨167,(7),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2713 : RecordDataValid section14Catalog 5 (⟨167,(7),[5,6],[174],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2714 : RecordDataValid section14Catalog 5 (⟨167,(8),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2715 : RecordDataValid section14Catalog 5 (⟨167,(8),[5,6],[174],971⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨971,[3,5,6,7],975⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2716 : RecordDataValid section14Catalog 5 (⟨167,(9),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2717 : RecordDataValid section14Catalog 5 (⟨167,(9),[5,6],[174],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2718 : RecordDataValid section14Catalog 5 (⟨167,(10),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2719 : RecordDataValid section14Catalog 5 (⟨167,(10),[5,6],[174],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2688_2720 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2688).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2688).take 32 = [⟨166,(11),[1,2,5,6,13,14],[170],648⟩,⟨166,(11),[5,6],[174],648⟩,⟨166,(12),[1,2,5,6,13,14],[170],649⟩,⟨166,(12),[5,6],[174],649⟩,⟨166,(13),[1,2,5,6,13,14],[170],649⟩,⟨166,(13),[5,6],[174],649⟩,⟨166,(14),[1,2,5,6,13,14],[170],649⟩,⟨166,(14),[5,6],[174],649⟩,⟨166,(15),[1,2,5,6,13,14],[170],649⟩,⟨166,(15),[5,6],[174],649⟩,⟨167,(0),[1,2,5,6,13,14],[170],418⟩,⟨167,(0),[5,6],[174],971⟩,⟨167,(1),[1,2,5,6,13,14],[170],419⟩,⟨167,(1),[5,6],[174],972⟩,⟨167,(2),[1,2,5,6,13,14],[170],420⟩,⟨167,(2),[5,6],[174],973⟩,⟨167,(3),[1,2,5,6,13,14],[170],421⟩,⟨167,(3),[5,6],[174],974⟩,⟨167,(4),[1,2,5,6,13,14],[170],422⟩,⟨167,(4),[5,6],[174],975⟩,⟨167,(5),[1,2,5,6,13,14],[170],419⟩,⟨167,(5),[5,6],[174],972⟩,⟨167,(6),[1,2,5,6,13,14],[170],420⟩,⟨167,(6),[5,6],[174],973⟩,⟨167,(7),[1,2,5,6,13,14],[170],421⟩,⟨167,(7),[5,6],[174],974⟩,⟨167,(8),[1,2,5,6,13,14],[170],418⟩,⟨167,(8),[5,6],[174],971⟩,⟨167,(9),[1,2,5,6,13,14],[170],419⟩,⟨167,(9),[5,6],[174],972⟩,⟨167,(10),[1,2,5,6,13,14],[170],420⟩,⟨167,(10),[5,6],[174],973⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2688
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2689
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2690
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2691
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2692
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2693
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2694
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2695
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2696
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2697
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2698
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2699
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2700
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2701
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2702
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2703
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2704
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2705
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2706
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2707
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2708
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2709
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2710
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2711
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2712
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2713
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2714
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2715
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2716
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2717
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2718
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2719
end Section14Records_5_2688_2720

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2688_2720


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2720_2752
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2720_2752
private theorem valid2720 : RecordDataValid section14Catalog 5 (⟨167,(11),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2721 : RecordDataValid section14Catalog 5 (⟨167,(11),[5,6],[174],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2722 : RecordDataValid section14Catalog 5 (⟨167,(12),[1,2,5,6,13,14],[170],423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨423,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2723 : RecordDataValid section14Catalog 5 (⟨167,(12),[5,6],[174],976⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨976,[3,5,6,7],980⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2724 : RecordDataValid section14Catalog 5 (⟨167,(13),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2725 : RecordDataValid section14Catalog 5 (⟨167,(13),[5,6],[174],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2726 : RecordDataValid section14Catalog 5 (⟨167,(14),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2727 : RecordDataValid section14Catalog 5 (⟨167,(14),[5,6],[174],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2728 : RecordDataValid section14Catalog 5 (⟨167,(15),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2729 : RecordDataValid section14Catalog 5 (⟨167,(15),[5,6],[174],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2730 : RecordDataValid section14Catalog 5 (⟨171,(0),[1,2,5,6,13,14],[170],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2731 : RecordDataValid section14Catalog 5 (⟨171,(0),[5,6],[174],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2732 : RecordDataValid section14Catalog 5 (⟨171,(1),[1,2,5,6,13,14],[170],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2733 : RecordDataValid section14Catalog 5 (⟨171,(1),[5,6],[174],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2734 : RecordDataValid section14Catalog 5 (⟨171,(2),[1,2,5,6,13,14],[170],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2735 : RecordDataValid section14Catalog 5 (⟨171,(2),[5,6],[174],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2736 : RecordDataValid section14Catalog 5 (⟨171,(3),[1,2,5,6,13,14],[170],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2737 : RecordDataValid section14Catalog 5 (⟨171,(3),[5,6],[174],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2738 : RecordDataValid section14Catalog 5 (⟨172,(0),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2739 : RecordDataValid section14Catalog 5 (⟨172,(0),[5,6],[174],977⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨977,[3,5,6,7],981⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2740 : RecordDataValid section14Catalog 5 (⟨172,(1),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2741 : RecordDataValid section14Catalog 5 (⟨172,(1),[5,6],[174],978⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨978,[3,5,6,7],982⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2742 : RecordDataValid section14Catalog 5 (⟨172,(2),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2743 : RecordDataValid section14Catalog 5 (⟨172,(2),[5,6],[174],979⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨979,[3,5,6,7],983⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2744 : RecordDataValid section14Catalog 5 (⟨172,(3),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2745 : RecordDataValid section14Catalog 5 (⟨172,(3),[5,6],[174],980⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨980,[3,5,6,7],984⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2746 : RecordDataValid section14Catalog 5 (⟨172,(4),[1,2,5,6,13,14],[170],432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨432,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2747 : RecordDataValid section14Catalog 5 (⟨172,(4),[5,6],[174],981⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨981,[3,5,6,7],985⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2748 : RecordDataValid section14Catalog 5 (⟨172,(5),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2749 : RecordDataValid section14Catalog 5 (⟨172,(5),[5,6],[174],978⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨978,[3,5,6,7],982⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2750 : RecordDataValid section14Catalog 5 (⟨172,(6),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2751 : RecordDataValid section14Catalog 5 (⟨172,(6),[5,6],[174],979⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨979,[3,5,6,7],983⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2720_2752 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2720).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2720).take 32 = [⟨167,(11),[1,2,5,6,13,14],[170],421⟩,⟨167,(11),[5,6],[174],974⟩,⟨167,(12),[1,2,5,6,13,14],[170],423⟩,⟨167,(12),[5,6],[174],976⟩,⟨167,(13),[1,2,5,6,13,14],[170],419⟩,⟨167,(13),[5,6],[174],972⟩,⟨167,(14),[1,2,5,6,13,14],[170],420⟩,⟨167,(14),[5,6],[174],973⟩,⟨167,(15),[1,2,5,6,13,14],[170],421⟩,⟨167,(15),[5,6],[174],974⟩,⟨171,(0),[1,2,5,6,13,14],[170],650⟩,⟨171,(0),[5,6],[174],650⟩,⟨171,(1),[1,2,5,6,13,14],[170],651⟩,⟨171,(1),[5,6],[174],651⟩,⟨171,(2),[1,2,5,6,13,14],[170],652⟩,⟨171,(2),[5,6],[174],652⟩,⟨171,(3),[1,2,5,6,13,14],[170],653⟩,⟨171,(3),[5,6],[174],653⟩,⟨172,(0),[1,2,5,6,13,14],[170],428⟩,⟨172,(0),[5,6],[174],977⟩,⟨172,(1),[1,2,5,6,13,14],[170],429⟩,⟨172,(1),[5,6],[174],978⟩,⟨172,(2),[1,2,5,6,13,14],[170],430⟩,⟨172,(2),[5,6],[174],979⟩,⟨172,(3),[1,2,5,6,13,14],[170],431⟩,⟨172,(3),[5,6],[174],980⟩,⟨172,(4),[1,2,5,6,13,14],[170],432⟩,⟨172,(4),[5,6],[174],981⟩,⟨172,(5),[1,2,5,6,13,14],[170],429⟩,⟨172,(5),[5,6],[174],978⟩,⟨172,(6),[1,2,5,6,13,14],[170],430⟩,⟨172,(6),[5,6],[174],979⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2720
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2721
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2722
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2723
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2724
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2725
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2726
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2727
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2728
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2729
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2730
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2731
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2732
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2733
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2734
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2735
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2736
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2737
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2738
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2739
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2740
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2741
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2742
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2743
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2744
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2745
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2746
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2747
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2748
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2749
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2750
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2751
end Section14Records_5_2720_2752

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2720_2752

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2688).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 2688 2720 2752 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_2688_2720 hnum) (Freiman.workReverse20260919_s0005_records_2720_2752 hnum))

#print axioms solution
