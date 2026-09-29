-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_2752_2816
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:27:45.787905+00:00
-- url     : https://prove2.me/submissions/3742e768-f7b7-4ec0-b054-090ae83e0097

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2752_2784
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2752_2784
private theorem valid2752 : RecordDataValid section14Catalog 5 (⟨172,(7),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2753 : RecordDataValid section14Catalog 5 (⟨172,(7),[5,6],[174],980⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨980,[3,5,6,7],984⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2754 : RecordDataValid section14Catalog 5 (⟨172,(8),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2755 : RecordDataValid section14Catalog 5 (⟨172,(8),[5,6],[174],977⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨977,[3,5,6,7],981⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2756 : RecordDataValid section14Catalog 5 (⟨172,(9),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2757 : RecordDataValid section14Catalog 5 (⟨172,(9),[5,6],[174],978⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨978,[3,5,6,7],982⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2758 : RecordDataValid section14Catalog 5 (⟨172,(10),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2759 : RecordDataValid section14Catalog 5 (⟨172,(10),[5,6],[174],979⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨979,[3,5,6,7],983⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2760 : RecordDataValid section14Catalog 5 (⟨172,(11),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2761 : RecordDataValid section14Catalog 5 (⟨172,(11),[5,6],[174],980⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨980,[3,5,6,7],984⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2762 : RecordDataValid section14Catalog 5 (⟨172,(12),[1,2,5,6,13,14],[170],433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨433,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2763 : RecordDataValid section14Catalog 5 (⟨172,(12),[5,6],[174],982⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨982,[3,5,6,7],986⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2764 : RecordDataValid section14Catalog 5 (⟨172,(13),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2765 : RecordDataValid section14Catalog 5 (⟨172,(13),[5,6],[174],978⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨978,[3,5,6,7],982⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2766 : RecordDataValid section14Catalog 5 (⟨172,(14),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2767 : RecordDataValid section14Catalog 5 (⟨172,(14),[5,6],[174],979⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨979,[3,5,6,7],983⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2768 : RecordDataValid section14Catalog 5 (⟨172,(15),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2769 : RecordDataValid section14Catalog 5 (⟨172,(15),[5,6],[174],980⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨980,[3,5,6,7],984⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2770 : RecordDataValid section14Catalog 5 (⟨175,(0),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2771 : RecordDataValid section14Catalog 5 (⟨175,(0),[5,6],[174],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2772 : RecordDataValid section14Catalog 5 (⟨175,(1),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2773 : RecordDataValid section14Catalog 5 (⟨175,(1),[5,6],[174],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2774 : RecordDataValid section14Catalog 5 (⟨175,(2),[1,2,5,6,13,14],[170],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2775 : RecordDataValid section14Catalog 5 (⟨175,(2),[5,6],[174],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2776 : RecordDataValid section14Catalog 5 (⟨175,(3),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2777 : RecordDataValid section14Catalog 5 (⟨175,(3),[5,6],[174],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2778 : RecordDataValid section14Catalog 5 (⟨175,(4),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2779 : RecordDataValid section14Catalog 5 (⟨175,(4),[5,6],[174],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2780 : RecordDataValid section14Catalog 5 (⟨175,(5),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2781 : RecordDataValid section14Catalog 5 (⟨175,(5),[5,6],[174],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2782 : RecordDataValid section14Catalog 5 (⟨175,(6),[1,2,5,6,13,14],[170],658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨658,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],659⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2783 : RecordDataValid section14Catalog 5 (⟨175,(6),[5,6],[174],658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨658,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],659⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2752_2784 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2752).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2752).take 32 = [⟨172,(7),[1,2,5,6,13,14],[170],431⟩,⟨172,(7),[5,6],[174],980⟩,⟨172,(8),[1,2,5,6,13,14],[170],428⟩,⟨172,(8),[5,6],[174],977⟩,⟨172,(9),[1,2,5,6,13,14],[170],429⟩,⟨172,(9),[5,6],[174],978⟩,⟨172,(10),[1,2,5,6,13,14],[170],430⟩,⟨172,(10),[5,6],[174],979⟩,⟨172,(11),[1,2,5,6,13,14],[170],431⟩,⟨172,(11),[5,6],[174],980⟩,⟨172,(12),[1,2,5,6,13,14],[170],433⟩,⟨172,(12),[5,6],[174],982⟩,⟨172,(13),[1,2,5,6,13,14],[170],429⟩,⟨172,(13),[5,6],[174],978⟩,⟨172,(14),[1,2,5,6,13,14],[170],430⟩,⟨172,(14),[5,6],[174],979⟩,⟨172,(15),[1,2,5,6,13,14],[170],431⟩,⟨172,(15),[5,6],[174],980⟩,⟨175,(0),[1,2,5,6,13,14],[170],654⟩,⟨175,(0),[5,6],[174],654⟩,⟨175,(1),[1,2,5,6,13,14],[170],655⟩,⟨175,(1),[5,6],[174],655⟩,⟨175,(2),[1,2,5,6,13,14],[170],656⟩,⟨175,(2),[5,6],[174],656⟩,⟨175,(3),[1,2,5,6,13,14],[170],657⟩,⟨175,(3),[5,6],[174],657⟩,⟨175,(4),[1,2,5,6,13,14],[170],654⟩,⟨175,(4),[5,6],[174],654⟩,⟨175,(5),[1,2,5,6,13,14],[170],655⟩,⟨175,(5),[5,6],[174],655⟩,⟨175,(6),[1,2,5,6,13,14],[170],658⟩,⟨175,(6),[5,6],[174],658⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2752
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2753
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2754
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2755
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2756
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2757
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2758
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2759
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2760
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2761
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2762
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2763
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2764
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2765
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2766
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2767
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2768
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2769
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2770
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2771
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2772
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2773
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2774
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2775
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2776
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2777
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2778
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2779
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2780
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2781
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2782
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2783
end Section14Records_5_2752_2784

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2752_2784


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2784_2816
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2784_2816
private theorem valid2784 : RecordDataValid section14Catalog 5 (⟨175,(7),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2785 : RecordDataValid section14Catalog 5 (⟨175,(7),[5,6],[174],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2786 : RecordDataValid section14Catalog 5 (⟨175,(8),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2787 : RecordDataValid section14Catalog 5 (⟨175,(8),[5,6],[174],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2788 : RecordDataValid section14Catalog 5 (⟨175,(9),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2789 : RecordDataValid section14Catalog 5 (⟨175,(9),[5,6],[174],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2790 : RecordDataValid section14Catalog 5 (⟨175,(10),[1,2,5,6,13,14],[170],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2791 : RecordDataValid section14Catalog 5 (⟨175,(10),[5,6],[174],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2792 : RecordDataValid section14Catalog 5 (⟨175,(11),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2793 : RecordDataValid section14Catalog 5 (⟨175,(11),[5,6],[174],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2794 : RecordDataValid section14Catalog 5 (⟨175,(12),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2795 : RecordDataValid section14Catalog 5 (⟨175,(12),[5,6],[174],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2796 : RecordDataValid section14Catalog 5 (⟨175,(13),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2797 : RecordDataValid section14Catalog 5 (⟨175,(13),[5,6],[174],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2798 : RecordDataValid section14Catalog 5 (⟨175,(14),[1,2,5,6,13,14],[170],659⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨659,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],660⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2799 : RecordDataValid section14Catalog 5 (⟨175,(14),[5,6],[174],659⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨659,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],660⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2800 : RecordDataValid section14Catalog 5 (⟨175,(15),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2801 : RecordDataValid section14Catalog 5 (⟨175,(15),[5,6],[174],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2802 : RecordDataValid section14Catalog 5 (⟨178,(0),[1,2,5,6,13,14],[170],660⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨660,[1,2,3,5,6,7,10,11,13,14,15],661⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2803 : RecordDataValid section14Catalog 5 (⟨178,(0),[5,6],[174],983⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨983,[3,5,6,7],987⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2804 : RecordDataValid section14Catalog 5 (⟨178,(1),[1,2,5,6,13,14],[170],661⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨661,[1,2,3,5,6,7,10,11,13,14,15],662⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2805 : RecordDataValid section14Catalog 5 (⟨178,(1),[5,6],[174],984⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨984,[3,5,6,7],988⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2806 : RecordDataValid section14Catalog 5 (⟨178,(2),[1,2,5,6,13,14],[170],660⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨660,[1,2,3,5,6,7,10,11,13,14,15],661⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2807 : RecordDataValid section14Catalog 5 (⟨178,(2),[5,6],[174],983⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨983,[3,5,6,7],987⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2808 : RecordDataValid section14Catalog 5 (⟨178,(3),[1,2,5,6,13,14],[170],662⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨662,[1,2,3,5,6,7,10,11,13,14,15],663⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2809 : RecordDataValid section14Catalog 5 (⟨178,(3),[5,6],[174],985⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨985,[3,5,6,7],989⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2810 : RecordDataValid section14Catalog 5 (⟨178,(4),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2811 : RecordDataValid section14Catalog 5 (⟨178,(4),[5,6],[174],986⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨986,[3,5,6,7],990⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2812 : RecordDataValid section14Catalog 5 (⟨178,(5),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2813 : RecordDataValid section14Catalog 5 (⟨178,(5),[5,6],[174],986⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨986,[3,5,6,7],990⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2814 : RecordDataValid section14Catalog 5 (⟨178,(6),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2815 : RecordDataValid section14Catalog 5 (⟨178,(6),[5,6],[174],986⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨986,[3,5,6,7],990⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2784_2816 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2784).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2784).take 32 = [⟨175,(7),[1,2,5,6,13,14],[170],657⟩,⟨175,(7),[5,6],[174],657⟩,⟨175,(8),[1,2,5,6,13,14],[170],654⟩,⟨175,(8),[5,6],[174],654⟩,⟨175,(9),[1,2,5,6,13,14],[170],655⟩,⟨175,(9),[5,6],[174],655⟩,⟨175,(10),[1,2,5,6,13,14],[170],656⟩,⟨175,(10),[5,6],[174],656⟩,⟨175,(11),[1,2,5,6,13,14],[170],657⟩,⟨175,(11),[5,6],[174],657⟩,⟨175,(12),[1,2,5,6,13,14],[170],654⟩,⟨175,(12),[5,6],[174],654⟩,⟨175,(13),[1,2,5,6,13,14],[170],655⟩,⟨175,(13),[5,6],[174],655⟩,⟨175,(14),[1,2,5,6,13,14],[170],659⟩,⟨175,(14),[5,6],[174],659⟩,⟨175,(15),[1,2,5,6,13,14],[170],657⟩,⟨175,(15),[5,6],[174],657⟩,⟨178,(0),[1,2,5,6,13,14],[170],660⟩,⟨178,(0),[5,6],[174],983⟩,⟨178,(1),[1,2,5,6,13,14],[170],661⟩,⟨178,(1),[5,6],[174],984⟩,⟨178,(2),[1,2,5,6,13,14],[170],660⟩,⟨178,(2),[5,6],[174],983⟩,⟨178,(3),[1,2,5,6,13,14],[170],662⟩,⟨178,(3),[5,6],[174],985⟩,⟨178,(4),[1,2,5,6,13,14],[170],663⟩,⟨178,(4),[5,6],[174],986⟩,⟨178,(5),[1,2,5,6,13,14],[170],663⟩,⟨178,(5),[5,6],[174],986⟩,⟨178,(6),[1,2,5,6,13,14],[170],663⟩,⟨178,(6),[5,6],[174],986⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2784
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2785
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2786
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2787
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2788
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2789
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2790
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2791
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2792
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2793
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2794
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2795
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2796
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2797
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2798
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2799
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2800
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2801
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2802
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2803
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2804
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2805
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2806
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2807
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2808
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2809
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2810
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2811
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2812
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2813
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2814
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2815
end Section14Records_5_2784_2816

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2784_2816

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2752).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 2752 2784 2816 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_2752_2784 hnum) (Freiman.workReverse20260919_s0005_records_2784_2816 hnum))

#print axioms solution
