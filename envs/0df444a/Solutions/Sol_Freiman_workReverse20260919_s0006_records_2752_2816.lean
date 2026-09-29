-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2752_2816
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:18:10.40481+00:00
-- url     : https://prove2.me/submissions/2adf81a7-8ba3-4c4e-8246-7c18f9d5aca0

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2752_2784
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2752_2784
private theorem valid2752 : RecordDataValid section14Catalog 6 (⟨192,(15),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2753 : RecordDataValid section14Catalog 6 (⟨192,(16),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2754 : RecordDataValid section14Catalog 6 (⟨192,(16),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2755 : RecordDataValid section14Catalog 6 (⟨192,(17),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2756 : RecordDataValid section14Catalog 6 (⟨192,(17),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2757 : RecordDataValid section14Catalog 6 (⟨192,(18),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2758 : RecordDataValid section14Catalog 6 (⟨192,(18),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2759 : RecordDataValid section14Catalog 6 (⟨192,(19),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2760 : RecordDataValid section14Catalog 6 (⟨192,(19),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2761 : RecordDataValid section14Catalog 6 (⟨192,(20),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2762 : RecordDataValid section14Catalog 6 (⟨192,(20),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2763 : RecordDataValid section14Catalog 6 (⟨192,(21),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2764 : RecordDataValid section14Catalog 6 (⟨192,(21),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2765 : RecordDataValid section14Catalog 6 (⟨192,(22),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2766 : RecordDataValid section14Catalog 6 (⟨192,(22),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2767 : RecordDataValid section14Catalog 6 (⟨192,(23),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2768 : RecordDataValid section14Catalog 6 (⟨192,(23),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2769 : RecordDataValid section14Catalog 6 (⟨192,(24),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2770 : RecordDataValid section14Catalog 6 (⟨192,(24),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2771 : RecordDataValid section14Catalog 6 (⟨195,(0),[1,2,5,6,13,14],[170],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2772 : RecordDataValid section14Catalog 6 (⟨195,(0),[5,6],[174],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2773 : RecordDataValid section14Catalog 6 (⟨195,(1),[1,2,5,6,13,14],[170],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2774 : RecordDataValid section14Catalog 6 (⟨195,(1),[5,6],[174],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2775 : RecordDataValid section14Catalog 6 (⟨195,(2),[1,2,5,6,13,14],[170],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2776 : RecordDataValid section14Catalog 6 (⟨195,(2),[5,6],[174],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2777 : RecordDataValid section14Catalog 6 (⟨195,(3),[1,2,5,6,13,14],[170],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2778 : RecordDataValid section14Catalog 6 (⟨195,(3),[5,6],[174],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2779 : RecordDataValid section14Catalog 6 (⟨195,(4),[1,2,5,6,13,14],[170],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2780 : RecordDataValid section14Catalog 6 (⟨195,(4),[5,6],[174],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2781 : RecordDataValid section14Catalog 6 (⟨195,(5),[1,2,5,6,13,14],[170],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2782 : RecordDataValid section14Catalog 6 (⟨195,(5),[5,6],[174],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2783 : RecordDataValid section14Catalog 6 (⟨195,(6),[1,2,5,6,13,14],[170],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2752_2784 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2752).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2752).take 32 = [⟨192,(15),[5,6],[174],1006⟩,⟨192,(16),[1,2,5,6,13,14],[170],446⟩,⟨192,(16),[5,6],[174],1006⟩,⟨192,(17),[1,2,5,6,13,14],[170],446⟩,⟨192,(17),[5,6],[174],1006⟩,⟨192,(18),[1,2,5,6,13,14],[170],446⟩,⟨192,(18),[5,6],[174],1006⟩,⟨192,(19),[1,2,5,6,13,14],[170],446⟩,⟨192,(19),[5,6],[174],1006⟩,⟨192,(20),[1,2,5,6,13,14],[170],447⟩,⟨192,(20),[5,6],[174],1007⟩,⟨192,(21),[1,2,5,6,13,14],[170],447⟩,⟨192,(21),[5,6],[174],1007⟩,⟨192,(22),[1,2,5,6,13,14],[170],447⟩,⟨192,(22),[5,6],[174],1007⟩,⟨192,(23),[1,2,5,6,13,14],[170],447⟩,⟨192,(23),[5,6],[174],1007⟩,⟨192,(24),[1,2,5,6,13,14],[170],447⟩,⟨192,(24),[5,6],[174],1007⟩,⟨195,(0),[1,2,5,6,13,14],[170],697⟩,⟨195,(0),[5,6],[174],697⟩,⟨195,(1),[1,2,5,6,13,14],[170],697⟩,⟨195,(1),[5,6],[174],697⟩,⟨195,(2),[1,2,5,6,13,14],[170],698⟩,⟨195,(2),[5,6],[174],698⟩,⟨195,(3),[1,2,5,6,13,14],[170],698⟩,⟨195,(3),[5,6],[174],698⟩,⟨195,(4),[1,2,5,6,13,14],[170],699⟩,⟨195,(4),[5,6],[174],699⟩,⟨195,(5),[1,2,5,6,13,14],[170],700⟩,⟨195,(5),[5,6],[174],700⟩,⟨195,(6),[1,2,5,6,13,14],[170],699⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2752
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2753
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2754
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2755
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2756
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2757
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2758
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2759
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2760
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2761
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2762
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2763
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2764
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2765
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2766
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2767
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2768
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2769
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2770
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2771
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2772
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2773
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2774
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2775
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2776
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2777
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2778
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2779
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2780
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2781
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2782
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2783
end Section14Records_6_2752_2784

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2752_2784


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2784_2816
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2784_2816
private theorem valid2784 : RecordDataValid section14Catalog 6 (⟨195,(6),[5,6],[174],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2785 : RecordDataValid section14Catalog 6 (⟨195,(7),[1,2,5,6,13,14],[170],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2786 : RecordDataValid section14Catalog 6 (⟨195,(7),[5,6],[174],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2787 : RecordDataValid section14Catalog 6 (⟨195,(8),[1,2,5,6,13,14],[170],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2788 : RecordDataValid section14Catalog 6 (⟨195,(8),[5,6],[174],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2789 : RecordDataValid section14Catalog 6 (⟨195,(9),[1,2,5,6,13,14],[170],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2790 : RecordDataValid section14Catalog 6 (⟨195,(9),[5,6],[174],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2791 : RecordDataValid section14Catalog 6 (⟨197,(0),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2792 : RecordDataValid section14Catalog 6 (⟨197,(0),[5,6],[174],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2793 : RecordDataValid section14Catalog 6 (⟨197,(1),[1,2,5,6,13,14],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2794 : RecordDataValid section14Catalog 6 (⟨197,(1),[5,6],[174],1009⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1009,[3,5,6,7],1013⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2795 : RecordDataValid section14Catalog 6 (⟨197,(2),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2796 : RecordDataValid section14Catalog 6 (⟨197,(2),[5,6],[174],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2797 : RecordDataValid section14Catalog 6 (⟨197,(3),[1,2,5,6,13,14],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2798 : RecordDataValid section14Catalog 6 (⟨197,(3),[5,6],[174],1010⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1010,[3,5,6,7],1014⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2799 : RecordDataValid section14Catalog 6 (⟨197,(4),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2800 : RecordDataValid section14Catalog 6 (⟨197,(4),[5,6],[174],1011⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1011,[3,5,6,7],1015⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2801 : RecordDataValid section14Catalog 6 (⟨197,(5),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2802 : RecordDataValid section14Catalog 6 (⟨197,(5),[5,6],[174],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2803 : RecordDataValid section14Catalog 6 (⟨197,(6),[1,2,5,6,13,14],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2804 : RecordDataValid section14Catalog 6 (⟨197,(6),[5,6],[174],1009⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1009,[3,5,6,7],1013⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2805 : RecordDataValid section14Catalog 6 (⟨197,(7),[1,2,5,6,13,14],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2806 : RecordDataValid section14Catalog 6 (⟨197,(7),[5,6],[174],1008⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1008,[3,5,6,7],1012⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2807 : RecordDataValid section14Catalog 6 (⟨197,(8),[1,2,5,6,13,14],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2808 : RecordDataValid section14Catalog 6 (⟨197,(8),[5,6],[174],1010⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1010,[3,5,6,7],1014⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2809 : RecordDataValid section14Catalog 6 (⟨197,(9),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2810 : RecordDataValid section14Catalog 6 (⟨197,(9),[5,6],[174],1011⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1011,[3,5,6,7],1015⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2811 : RecordDataValid section14Catalog 6 (⟨197,(10),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2812 : RecordDataValid section14Catalog 6 (⟨197,(10),[5,6],[174],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2813 : RecordDataValid section14Catalog 6 (⟨197,(11),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2814 : RecordDataValid section14Catalog 6 (⟨197,(11),[5,6],[174],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2815 : RecordDataValid section14Catalog 6 (⟨197,(12),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2784_2816 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2784).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2784).take 32 = [⟨195,(6),[5,6],[174],699⟩,⟨195,(7),[1,2,5,6,13,14],[170],701⟩,⟨195,(7),[5,6],[174],701⟩,⟨195,(8),[1,2,5,6,13,14],[170],702⟩,⟨195,(8),[5,6],[174],702⟩,⟨195,(9),[1,2,5,6,13,14],[170],703⟩,⟨195,(9),[5,6],[174],703⟩,⟨197,(0),[1,2,5,6,13,14],[170],453⟩,⟨197,(0),[5,6],[174],1008⟩,⟨197,(1),[1,2,5,6,13,14],[170],454⟩,⟨197,(1),[5,6],[174],1009⟩,⟨197,(2),[1,2,5,6,13,14],[170],453⟩,⟨197,(2),[5,6],[174],1008⟩,⟨197,(3),[1,2,5,6,13,14],[170],455⟩,⟨197,(3),[5,6],[174],1010⟩,⟨197,(4),[1,2,5,6,13,14],[170],456⟩,⟨197,(4),[5,6],[174],1011⟩,⟨197,(5),[1,2,5,6,13,14],[170],453⟩,⟨197,(5),[5,6],[174],1008⟩,⟨197,(6),[1,2,5,6,13,14],[170],454⟩,⟨197,(6),[5,6],[174],1009⟩,⟨197,(7),[1,2,5,6,13,14],[170],453⟩,⟨197,(7),[5,6],[174],1008⟩,⟨197,(8),[1,2,5,6,13,14],[170],455⟩,⟨197,(8),[5,6],[174],1010⟩,⟨197,(9),[1,2,5,6,13,14],[170],456⟩,⟨197,(9),[5,6],[174],1011⟩,⟨197,(10),[1,2,5,6,13,14],[170],457⟩,⟨197,(10),[5,6],[174],1012⟩,⟨197,(11),[1,2,5,6,13,14],[170],457⟩,⟨197,(11),[5,6],[174],1012⟩,⟨197,(12),[1,2,5,6,13,14],[170],457⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2784
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2785
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2786
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2787
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2788
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2789
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2790
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2791
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2792
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2793
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2794
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2795
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2796
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2797
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2798
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2799
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2800
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2801
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2802
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2803
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2804
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2805
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2806
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2807
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2808
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2809
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2810
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2811
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2812
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2813
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2814
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2815
end Section14Records_6_2784_2816

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2784_2816

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2752).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2752 2784 2816 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2752_2784 hnum) (Freiman.workReverse20260919_s0006_records_2784_2816 hnum))

#print axioms solution
