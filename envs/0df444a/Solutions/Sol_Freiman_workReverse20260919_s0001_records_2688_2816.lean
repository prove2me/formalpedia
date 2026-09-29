-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_2688_2816
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:58:57.476567+00:00
-- url     : https://prove2.me/submissions/bb1cece8-e8e9-4cfc-84da-d581aa2a8e2f

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2688_2720
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2688_2720
private theorem valid2688 : RecordDataValid section14Catalog 1 (⟨124,(5),[1,5,6,13],[170],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2689 : RecordDataValid section14Catalog 1 (⟨124,(6),[1,5,6,13],[170],492⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨492,[1,4,5,6,8,9,10,12,13,16],493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2690 : RecordDataValid section14Catalog 1 (⟨124,(7),[1,5,6,13],[170],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2691 : RecordDataValid section14Catalog 1 (⟨124,(8),[1,5,6,13],[170],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2692 : RecordDataValid section14Catalog 1 (⟨124,(9),[1,5,6,13],[170],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2693 : RecordDataValid section14Catalog 1 (⟨124,(10),[1,5,6,13],[170],490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨490,[1,4,5,6,8,9,10,12,13,16],491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2694 : RecordDataValid section14Catalog 1 (⟨124,(11),[1,5,6,13],[170],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2695 : RecordDataValid section14Catalog 1 (⟨124,(12),[1,5,6,13],[170],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2696 : RecordDataValid section14Catalog 1 (⟨124,(13),[1,5,6,13],[170],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2697 : RecordDataValid section14Catalog 1 (⟨124,(14),[1,5,6,13],[170],493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨493,[1,4,5,6,8,9,10,12,13,16],494⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2698 : RecordDataValid section14Catalog 1 (⟨124,(15),[1,5,6,13],[170],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2699 : RecordDataValid section14Catalog 1 (⟨127,(0),[1,5,6,13],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2700 : RecordDataValid section14Catalog 1 (⟨127,(1),[1,5,6,13],[170],495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨495,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2701 : RecordDataValid section14Catalog 1 (⟨127,(2),[1,5,6,13],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2702 : RecordDataValid section14Catalog 1 (⟨127,(3),[1,5,6,13],[170],496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨496,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2703 : RecordDataValid section14Catalog 1 (⟨127,(4),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2704 : RecordDataValid section14Catalog 1 (⟨127,(5),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2705 : RecordDataValid section14Catalog 1 (⟨127,(6),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2706 : RecordDataValid section14Catalog 1 (⟨127,(7),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2707 : RecordDataValid section14Catalog 1 (⟨127,(8),[1,5,6,13],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2708 : RecordDataValid section14Catalog 1 (⟨127,(9),[1,5,6,13],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2709 : RecordDataValid section14Catalog 1 (⟨127,(10),[1,5,6,13],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2710 : RecordDataValid section14Catalog 1 (⟨127,(11),[1,5,6,13],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2711 : RecordDataValid section14Catalog 1 (⟨127,(12),[1,5,6,13],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2712 : RecordDataValid section14Catalog 1 (⟨127,(13),[1,5,6,13],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2713 : RecordDataValid section14Catalog 1 (⟨127,(14),[1,5,6,13],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2714 : RecordDataValid section14Catalog 1 (⟨127,(15),[1,5,6,13],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2715 : RecordDataValid section14Catalog 1 (⟨129,(0),[1,5,6],[170],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2716 : RecordDataValid section14Catalog 1 (⟨129,(1),[1,5,6],[170],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2717 : RecordDataValid section14Catalog 1 (⟨129,(2),[1,5,6],[170],502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨502,[1,4,5,6,8,9,10,12],503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2718 : RecordDataValid section14Catalog 1 (⟨129,(3),[1,5,6],[170],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2719 : RecordDataValid section14Catalog 1 (⟨129,(4),[1,5,6],[170],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2688_2720 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2688).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2688).take 32 = [⟨124,(5),[1,5,6,13],[170],489⟩,⟨124,(6),[1,5,6,13],[170],492⟩,⟨124,(7),[1,5,6,13],[170],491⟩,⟨124,(8),[1,5,6,13],[170],488⟩,⟨124,(9),[1,5,6,13],[170],489⟩,⟨124,(10),[1,5,6,13],[170],490⟩,⟨124,(11),[1,5,6,13],[170],491⟩,⟨124,(12),[1,5,6,13],[170],488⟩,⟨124,(13),[1,5,6,13],[170],489⟩,⟨124,(14),[1,5,6,13],[170],493⟩,⟨124,(15),[1,5,6,13],[170],491⟩,⟨127,(0),[1,5,6,13],[170],494⟩,⟨127,(1),[1,5,6,13],[170],495⟩,⟨127,(2),[1,5,6,13],[170],494⟩,⟨127,(3),[1,5,6,13],[170],496⟩,⟨127,(4),[1,5,6,13],[170],497⟩,⟨127,(5),[1,5,6,13],[170],497⟩,⟨127,(6),[1,5,6,13],[170],497⟩,⟨127,(7),[1,5,6,13],[170],497⟩,⟨127,(8),[1,5,6,13],[170],498⟩,⟨127,(9),[1,5,6,13],[170],498⟩,⟨127,(10),[1,5,6,13],[170],498⟩,⟨127,(11),[1,5,6,13],[170],498⟩,⟨127,(12),[1,5,6,13],[170],499⟩,⟨127,(13),[1,5,6,13],[170],499⟩,⟨127,(14),[1,5,6,13],[170],499⟩,⟨127,(15),[1,5,6,13],[170],499⟩,⟨129,(0),[1,5,6],[170],500⟩,⟨129,(1),[1,5,6],[170],501⟩,⟨129,(2),[1,5,6],[170],502⟩,⟨129,(3),[1,5,6],[170],503⟩,⟨129,(4),[1,5,6],[170],500⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2688
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2689
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2690
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2691
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2692
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2693
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2694
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2695
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2696
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2697
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2698
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2699
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2700
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2701
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2702
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2703
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2704
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2705
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2706
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2707
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2708
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2709
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2710
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2711
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2712
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2713
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2714
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2715
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2716
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2717
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2718
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2719
end Section14Records_1_2688_2720

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2688_2720


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2720_2752
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2720_2752
private theorem valid2720 : RecordDataValid section14Catalog 1 (⟨129,(5),[1,5,6],[170],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2721 : RecordDataValid section14Catalog 1 (⟨129,(6),[1,5,6],[170],504⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨504,[1,4,5,6,8,9,10,12],505⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2722 : RecordDataValid section14Catalog 1 (⟨129,(7),[1,5,6],[170],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2723 : RecordDataValid section14Catalog 1 (⟨129,(8),[1,5,6],[170],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2724 : RecordDataValid section14Catalog 1 (⟨129,(9),[1,5,6],[170],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2725 : RecordDataValid section14Catalog 1 (⟨129,(10),[1,5,6],[170],502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨502,[1,4,5,6,8,9,10,12],503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2726 : RecordDataValid section14Catalog 1 (⟨129,(11),[1,5,6],[170],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2727 : RecordDataValid section14Catalog 1 (⟨129,(12),[1,5,6],[170],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2728 : RecordDataValid section14Catalog 1 (⟨129,(13),[1,5,6],[170],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2729 : RecordDataValid section14Catalog 1 (⟨129,(14),[1,5,6],[170],505⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨505,[1,4,5,6,8,9,10,12],506⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2730 : RecordDataValid section14Catalog 1 (⟨129,(15),[1,5,6],[170],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2731 : RecordDataValid section14Catalog 1 (⟨132,(0),[1,5,6],[170],506⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨506,[1,2,3,4,5,6,7,8,9,10,11,12],507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2732 : RecordDataValid section14Catalog 1 (⟨132,(1),[1,5,6],[170],507⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨507,[1,2,3,4,5,6,7,8,9,10,11,12],508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2733 : RecordDataValid section14Catalog 1 (⟨132,(2),[1,5,6],[170],508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨508,[1,2,3,4,5,6,7,8,9,10,11,12],509⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2734 : RecordDataValid section14Catalog 1 (⟨132,(3),[1,5,6],[170],509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨509,[1,2,3,4,5,6,7,8,9,10,11,12],510⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2735 : RecordDataValid section14Catalog 1 (⟨134,(0),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2736 : RecordDataValid section14Catalog 1 (⟨134,(1),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2737 : RecordDataValid section14Catalog 1 (⟨134,(2),[1,5,6,13],[170],510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨510,[1,5,6,9,10,13],511⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2738 : RecordDataValid section14Catalog 1 (⟨134,(3),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2739 : RecordDataValid section14Catalog 1 (⟨134,(4),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2740 : RecordDataValid section14Catalog 1 (⟨134,(5),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2741 : RecordDataValid section14Catalog 1 (⟨134,(6),[1,5,6,13],[170],511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨511,[1,2,5,6,9,10,13,14],512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2742 : RecordDataValid section14Catalog 1 (⟨134,(7),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2743 : RecordDataValid section14Catalog 1 (⟨134,(8),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2744 : RecordDataValid section14Catalog 1 (⟨134,(9),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2745 : RecordDataValid section14Catalog 1 (⟨134,(10),[1,5,6,13],[170],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2746 : RecordDataValid section14Catalog 1 (⟨134,(11),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2747 : RecordDataValid section14Catalog 1 (⟨134,(12),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2748 : RecordDataValid section14Catalog 1 (⟨134,(13),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2749 : RecordDataValid section14Catalog 1 (⟨134,(14),[1,5,6,13],[170],513⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨513,[1,2,5,6,9,10,13,14],514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2750 : RecordDataValid section14Catalog 1 (⟨134,(15),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2751 : RecordDataValid section14Catalog 1 (⟨134,(16),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2720_2752 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2720).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2720).take 32 = [⟨129,(5),[1,5,6],[170],501⟩,⟨129,(6),[1,5,6],[170],504⟩,⟨129,(7),[1,5,6],[170],503⟩,⟨129,(8),[1,5,6],[170],500⟩,⟨129,(9),[1,5,6],[170],501⟩,⟨129,(10),[1,5,6],[170],502⟩,⟨129,(11),[1,5,6],[170],503⟩,⟨129,(12),[1,5,6],[170],500⟩,⟨129,(13),[1,5,6],[170],501⟩,⟨129,(14),[1,5,6],[170],505⟩,⟨129,(15),[1,5,6],[170],503⟩,⟨132,(0),[1,5,6],[170],506⟩,⟨132,(1),[1,5,6],[170],507⟩,⟨132,(2),[1,5,6],[170],508⟩,⟨132,(3),[1,5,6],[170],509⟩,⟨134,(0),[1,5,6,13],[170],3⟩,⟨134,(1),[1,5,6,13],[170],3⟩,⟨134,(2),[1,5,6,13],[170],510⟩,⟨134,(3),[1,5,6,13],[170],29⟩,⟨134,(4),[1,5,6,13],[170],3⟩,⟨134,(5),[1,5,6,13],[170],3⟩,⟨134,(6),[1,5,6,13],[170],511⟩,⟨134,(7),[1,5,6,13],[170],29⟩,⟨134,(8),[1,5,6,13],[170],3⟩,⟨134,(9),[1,5,6,13],[170],3⟩,⟨134,(10),[1,5,6,13],[170],512⟩,⟨134,(11),[1,5,6,13],[170],29⟩,⟨134,(12),[1,5,6,13],[170],3⟩,⟨134,(13),[1,5,6,13],[170],3⟩,⟨134,(14),[1,5,6,13],[170],513⟩,⟨134,(15),[1,5,6,13],[170],29⟩,⟨134,(16),[1,5,6,13],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2720
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2721
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2722
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2723
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2724
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2725
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2726
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2727
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2728
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2729
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2730
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2731
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2732
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2733
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2734
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2735
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2736
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2737
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2738
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2739
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2740
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2741
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2742
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2743
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2744
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2745
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2746
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2747
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2748
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2749
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2750
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2751
end Section14Records_1_2720_2752

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2720_2752


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2752_2784
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2752_2784
private theorem valid2752 : RecordDataValid section14Catalog 1 (⟨134,(17),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2753 : RecordDataValid section14Catalog 1 (⟨134,(18),[1,5,6,13],[170],514⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨514,[1,2,4,5,6,8,9,10,12,13,14,16],515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2754 : RecordDataValid section14Catalog 1 (⟨134,(19),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2755 : RecordDataValid section14Catalog 1 (⟨135,(0),[1,5,6,13],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2756 : RecordDataValid section14Catalog 1 (⟨135,(1),[1,5,6,13],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2757 : RecordDataValid section14Catalog 1 (⟨135,(2),[1,5,6,13],[170],516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨516,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2758 : RecordDataValid section14Catalog 1 (⟨135,(3),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2759 : RecordDataValid section14Catalog 1 (⟨135,(4),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2760 : RecordDataValid section14Catalog 1 (⟨135,(5),[1,5,6,13],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2761 : RecordDataValid section14Catalog 1 (⟨135,(6),[1,5,6,13],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2762 : RecordDataValid section14Catalog 1 (⟨135,(7),[1,5,6,13],[170],516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨516,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2763 : RecordDataValid section14Catalog 1 (⟨135,(8),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2764 : RecordDataValid section14Catalog 1 (⟨135,(9),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2765 : RecordDataValid section14Catalog 1 (⟨135,(10),[1,5,6,13],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2766 : RecordDataValid section14Catalog 1 (⟨135,(11),[1,5,6,13],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2767 : RecordDataValid section14Catalog 1 (⟨135,(12),[1,5,6,13],[170],520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨520,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],521⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2768 : RecordDataValid section14Catalog 1 (⟨135,(13),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2769 : RecordDataValid section14Catalog 1 (⟨135,(14),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2770 : RecordDataValid section14Catalog 1 (⟨135,(15),[1,5,6,13],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2771 : RecordDataValid section14Catalog 1 (⟨135,(16),[1,5,6,13],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2772 : RecordDataValid section14Catalog 1 (⟨135,(17),[1,5,6,13],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2773 : RecordDataValid section14Catalog 1 (⟨135,(18),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2774 : RecordDataValid section14Catalog 1 (⟨135,(19),[1,5,6,13],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2775 : RecordDataValid section14Catalog 1 (⟨135,(20),[1,5,6,13],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2776 : RecordDataValid section14Catalog 1 (⟨135,(21),[1,5,6,13],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2777 : RecordDataValid section14Catalog 1 (⟨135,(22),[1,5,6,13],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2778 : RecordDataValid section14Catalog 1 (⟨135,(23),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2779 : RecordDataValid section14Catalog 1 (⟨135,(24),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2780 : RecordDataValid section14Catalog 1 (⟨136,(0),[1,6,13],[170],523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨523,[1,4,5,6,8,9,10,12,13,16],524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2781 : RecordDataValid section14Catalog 1 (⟨136,(1),[1,5,6,13],[170],524⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨524,[1,4,5,6,8,9,10,12,13,16],525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2782 : RecordDataValid section14Catalog 1 (⟨136,(2),[1,5,6,13],[170],524⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨524,[1,4,5,6,8,9,10,12,13,16],525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2783 : RecordDataValid section14Catalog 1 (⟨136,(3),[1,5,6,13],[170],524⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨524,[1,4,5,6,8,9,10,12,13,16],525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2752_2784 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2752).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2752).take 32 = [⟨134,(17),[1,5,6,13],[170],3⟩,⟨134,(18),[1,5,6,13],[170],514⟩,⟨134,(19),[1,5,6,13],[170],29⟩,⟨135,(0),[1,5,6,13],[170],515⟩,⟨135,(1),[1,5,6,13],[170],515⟩,⟨135,(2),[1,5,6,13],[170],516⟩,⟨135,(3),[1,5,6,13],[170],517⟩,⟨135,(4),[1,5,6,13],[170],518⟩,⟨135,(5),[1,5,6,13],[170],515⟩,⟨135,(6),[1,5,6,13],[170],515⟩,⟨135,(7),[1,5,6,13],[170],516⟩,⟨135,(8),[1,5,6,13],[170],517⟩,⟨135,(9),[1,5,6,13],[170],518⟩,⟨135,(10),[1,5,6,13],[170],519⟩,⟨135,(11),[1,5,6,13],[170],519⟩,⟨135,(12),[1,5,6,13],[170],520⟩,⟨135,(13),[1,5,6,13],[170],517⟩,⟨135,(14),[1,5,6,13],[170],518⟩,⟨135,(15),[1,5,6,13],[170],521⟩,⟨135,(16),[1,5,6,13],[170],521⟩,⟨135,(17),[1,5,6,13],[170],521⟩,⟨135,(18),[1,5,6,13],[170],517⟩,⟨135,(19),[1,5,6,13],[170],521⟩,⟨135,(20),[1,5,6,13],[170],522⟩,⟨135,(21),[1,5,6,13],[170],522⟩,⟨135,(22),[1,5,6,13],[170],522⟩,⟨135,(23),[1,5,6,13],[170],517⟩,⟨135,(24),[1,5,6,13],[170],518⟩,⟨136,(0),[1,6,13],[170],523⟩,⟨136,(1),[1,5,6,13],[170],524⟩,⟨136,(2),[1,5,6,13],[170],524⟩,⟨136,(3),[1,5,6,13],[170],524⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2752
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2753
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2754
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2755
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2756
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2757
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2758
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2759
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2760
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2761
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2762
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2763
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2764
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2765
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2766
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2767
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2768
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2769
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2770
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2771
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2772
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2773
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2774
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2775
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2776
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2777
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2778
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2779
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2780
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2781
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2782
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2783
end Section14Records_1_2752_2784

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2752_2784


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2784_2816
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2784_2816
private theorem valid2784 : RecordDataValid section14Catalog 1 (⟨136,(4),[1,5,6,13],[170],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2785 : RecordDataValid section14Catalog 1 (⟨136,(5),[1,5,6,13],[170],523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨523,[1,4,5,6,8,9,10,12,13,16],524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2786 : RecordDataValid section14Catalog 1 (⟨136,(6),[1,6,13],[170],526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨526,[1,4,5,6,8,9,10,12,13,16],527⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2787 : RecordDataValid section14Catalog 1 (⟨136,(7),[1,5,6,13],[170],527⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨527,[1,4,5,6,8,9,10,12,13,16],528⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2788 : RecordDataValid section14Catalog 1 (⟨136,(8),[1,5,6,13],[170],527⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨527,[1,4,5,6,8,9,10,12,13,16],528⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2789 : RecordDataValid section14Catalog 1 (⟨136,(9),[1,5,6,13],[170],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2790 : RecordDataValid section14Catalog 1 (⟨136,(10),[1,5,6,13],[170],523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨523,[1,4,5,6,8,9,10,12,13,16],524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2791 : RecordDataValid section14Catalog 1 (⟨136,(11),[1,5,6,13],[170],526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨526,[1,4,5,6,8,9,10,12,13,16],527⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2792 : RecordDataValid section14Catalog 1 (⟨136,(12),[1,5,6,13],[170],529⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨529,[1,4,5,6,8,9,10,12,13,16],530⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2793 : RecordDataValid section14Catalog 1 (⟨136,(13),[1,5,6,13],[170],530⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨530,[1,4,5,6,8,9,10,12,13,16],531⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2794 : RecordDataValid section14Catalog 1 (⟨136,(14),[1,5,6,13],[170],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2795 : RecordDataValid section14Catalog 1 (⟨136,(15),[1,5,6,13],[170],523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨523,[1,4,5,6,8,9,10,12,13,16],524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2796 : RecordDataValid section14Catalog 1 (⟨136,(16),[1,5,6,13],[170],526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨526,[1,4,5,6,8,9,10,12,13,16],527⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2797 : RecordDataValid section14Catalog 1 (⟨136,(17),[1,5,6,13],[170],532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨532,[1,4,5,6,8,9,10,12,13,16],533⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2798 : RecordDataValid section14Catalog 1 (⟨136,(18),[1,5,6,13],[170],533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨533,[1,4,5,6,8,9,10,12,13,16],534⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2799 : RecordDataValid section14Catalog 1 (⟨136,(19),[1,5,6,13],[170],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2800 : RecordDataValid section14Catalog 1 (⟨136,(20),[1,5,6,13],[170],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2801 : RecordDataValid section14Catalog 1 (⟨136,(21),[1,5,6,13],[170],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2802 : RecordDataValid section14Catalog 1 (⟨136,(22),[1,5,6,13],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2803 : RecordDataValid section14Catalog 1 (⟨136,(23),[1,5,6,13],[170],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2804 : RecordDataValid section14Catalog 1 (⟨136,(24),[1,5,6,13],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2805 : RecordDataValid section14Catalog 1 (⟨138,(0),[1,5,6,13],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2806 : RecordDataValid section14Catalog 1 (⟨138,(1),[1,5,6,13],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2807 : RecordDataValid section14Catalog 1 (⟨138,(2),[1,5,6,13],[170],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2808 : RecordDataValid section14Catalog 1 (⟨138,(3),[1,5,6,13],[170],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2809 : RecordDataValid section14Catalog 1 (⟨138,(4),[1,5,6,13],[170],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2810 : RecordDataValid section14Catalog 1 (⟨138,(5),[1,5,6,13],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2811 : RecordDataValid section14Catalog 1 (⟨138,(6),[1,5,6,13],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2812 : RecordDataValid section14Catalog 1 (⟨138,(7),[1,5,6,13],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2813 : RecordDataValid section14Catalog 1 (⟨138,(8),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2814 : RecordDataValid section14Catalog 1 (⟨138,(9),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2815 : RecordDataValid section14Catalog 1 (⟨138,(10),[1,5,6,13],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2784_2816 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2784).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2784).take 32 = [⟨136,(4),[1,5,6,13],[170],525⟩,⟨136,(5),[1,5,6,13],[170],523⟩,⟨136,(6),[1,6,13],[170],526⟩,⟨136,(7),[1,5,6,13],[170],527⟩,⟨136,(8),[1,5,6,13],[170],527⟩,⟨136,(9),[1,5,6,13],[170],528⟩,⟨136,(10),[1,5,6,13],[170],523⟩,⟨136,(11),[1,5,6,13],[170],526⟩,⟨136,(12),[1,5,6,13],[170],529⟩,⟨136,(13),[1,5,6,13],[170],530⟩,⟨136,(14),[1,5,6,13],[170],531⟩,⟨136,(15),[1,5,6,13],[170],523⟩,⟨136,(16),[1,5,6,13],[170],526⟩,⟨136,(17),[1,5,6,13],[170],532⟩,⟨136,(18),[1,5,6,13],[170],533⟩,⟨136,(19),[1,5,6,13],[170],534⟩,⟨136,(20),[1,5,6,13],[170],535⟩,⟨136,(21),[1,5,6,13],[170],536⟩,⟨136,(22),[1,5,6,13],[170],537⟩,⟨136,(23),[1,5,6,13],[170],538⟩,⟨136,(24),[1,5,6,13],[170],537⟩,⟨138,(0),[1,5,6,13],[170],539⟩,⟨138,(1),[1,5,6,13],[170],539⟩,⟨138,(2),[1,5,6,13],[170],540⟩,⟨138,(3),[1,5,6,13],[170],541⟩,⟨138,(4),[1,5,6,13],[170],542⟩,⟨138,(5),[1,5,6,13],[170],543⟩,⟨138,(6),[1,5,6,13],[170],543⟩,⟨138,(7),[1,5,6,13],[170],544⟩,⟨138,(8),[1,5,6,13],[170],517⟩,⟨138,(9),[1,5,6,13],[170],518⟩,⟨138,(10),[1,5,6,13],[170],545⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2784
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2785
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2786
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2787
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2788
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2789
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2790
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2791
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2792
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2793
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2794
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2795
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2796
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2797
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2798
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2799
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2800
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2801
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2802
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2803
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2804
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2805
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2806
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2807
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2808
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2809
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2810
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2811
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2812
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2813
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2814
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2815
end Section14Records_1_2784_2816

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2784_2816

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2688).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 2688 2752 2816 (by decide) (by decide) (all_of_interval_split P xs 2688 2720 2752 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_2688_2720 hnum) (Freiman.workReverse20260919_s0001_records_2720_2752 hnum)) (all_of_interval_split P xs 2752 2784 2816 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_2752_2784 hnum) (Freiman.workReverse20260919_s0001_records_2784_2816 hnum)))

#print axioms solution
