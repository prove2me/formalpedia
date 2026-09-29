-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2816_2880
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:18:16.068632+00:00
-- url     : https://prove2.me/submissions/4e7f453a-8a9b-42ab-ba67-f74a84e3ca64

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2816_2848
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2816_2848
private theorem valid2816 : RecordDataValid section14Catalog 6 (⟨197,(12),[5,6],[174],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2817 : RecordDataValid section14Catalog 6 (⟨197,(13),[1,2,5,6,13,14],[170],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2818 : RecordDataValid section14Catalog 6 (⟨197,(13),[5,6],[174],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2819 : RecordDataValid section14Catalog 6 (⟨197,(14),[1,2,5,6,13,14],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2820 : RecordDataValid section14Catalog 6 (⟨197,(14),[5,6],[174],1011⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1011,[3,5,6,7],1015⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2821 : RecordDataValid section14Catalog 6 (⟨197,(15),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2822 : RecordDataValid section14Catalog 6 (⟨197,(15),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2823 : RecordDataValid section14Catalog 6 (⟨197,(16),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2824 : RecordDataValid section14Catalog 6 (⟨197,(16),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2825 : RecordDataValid section14Catalog 6 (⟨197,(17),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2826 : RecordDataValid section14Catalog 6 (⟨197,(17),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2827 : RecordDataValid section14Catalog 6 (⟨197,(18),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2828 : RecordDataValid section14Catalog 6 (⟨197,(18),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2829 : RecordDataValid section14Catalog 6 (⟨197,(19),[1,2,5,6,13,14],[170],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2830 : RecordDataValid section14Catalog 6 (⟨197,(19),[5,6],[174],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2831 : RecordDataValid section14Catalog 6 (⟨197,(20),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2832 : RecordDataValid section14Catalog 6 (⟨197,(20),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2833 : RecordDataValid section14Catalog 6 (⟨197,(21),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2834 : RecordDataValid section14Catalog 6 (⟨197,(21),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2835 : RecordDataValid section14Catalog 6 (⟨197,(22),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2836 : RecordDataValid section14Catalog 6 (⟨197,(22),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2837 : RecordDataValid section14Catalog 6 (⟨197,(23),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2838 : RecordDataValid section14Catalog 6 (⟨197,(23),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2839 : RecordDataValid section14Catalog 6 (⟨197,(24),[1,2,5,6,13,14],[170],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2840 : RecordDataValid section14Catalog 6 (⟨197,(24),[5,6],[174],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2841 : RecordDataValid section14Catalog 6 (⟨200,(0),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2842 : RecordDataValid section14Catalog 6 (⟨200,(0),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2843 : RecordDataValid section14Catalog 6 (⟨200,(1),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2844 : RecordDataValid section14Catalog 6 (⟨200,(1),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2845 : RecordDataValid section14Catalog 6 (⟨200,(2),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2846 : RecordDataValid section14Catalog 6 (⟨200,(2),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2847 : RecordDataValid section14Catalog 6 (⟨200,(3),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2816_2848 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2816).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2816).take 32 = [⟨197,(12),[5,6],[174],1012⟩,⟨197,(13),[1,2,5,6,13,14],[170],457⟩,⟨197,(13),[5,6],[174],1012⟩,⟨197,(14),[1,2,5,6,13,14],[170],456⟩,⟨197,(14),[5,6],[174],1011⟩,⟨197,(15),[1,2,5,6,13,14],[170],458⟩,⟨197,(15),[5,6],[174],1013⟩,⟨197,(16),[1,2,5,6,13,14],[170],458⟩,⟨197,(16),[5,6],[174],1013⟩,⟨197,(17),[1,2,5,6,13,14],[170],458⟩,⟨197,(17),[5,6],[174],1013⟩,⟨197,(18),[1,2,5,6,13,14],[170],458⟩,⟨197,(18),[5,6],[174],1013⟩,⟨197,(19),[1,2,5,6,13,14],[170],458⟩,⟨197,(19),[5,6],[174],1013⟩,⟨197,(20),[1,2,5,6,13,14],[170],459⟩,⟨197,(20),[5,6],[174],1014⟩,⟨197,(21),[1,2,5,6,13,14],[170],459⟩,⟨197,(21),[5,6],[174],1014⟩,⟨197,(22),[1,2,5,6,13,14],[170],459⟩,⟨197,(22),[5,6],[174],1014⟩,⟨197,(23),[1,2,5,6,13,14],[170],459⟩,⟨197,(23),[5,6],[174],1014⟩,⟨197,(24),[1,2,5,6,13,14],[170],459⟩,⟨197,(24),[5,6],[174],1014⟩,⟨200,(0),[1,2,5,6,13,14],[170],704⟩,⟨200,(0),[5,6],[174],704⟩,⟨200,(1),[1,2,5,6,13,14],[170],704⟩,⟨200,(1),[5,6],[174],704⟩,⟨200,(2),[1,2,5,6,13,14],[170],704⟩,⟨200,(2),[5,6],[174],704⟩,⟨200,(3),[1,2,5,6,13,14],[170],704⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2816
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2817
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2818
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2819
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2820
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2821
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2822
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2823
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2824
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2825
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2826
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2827
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2828
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2829
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2830
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2831
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2832
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2833
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2834
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2835
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2836
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2837
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2838
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2839
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2840
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2841
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2842
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2843
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2844
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2845
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2846
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2847
end Section14Records_6_2816_2848

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2816_2848


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2848_2880
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2848_2880
private theorem valid2848 : RecordDataValid section14Catalog 6 (⟨200,(3),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2849 : RecordDataValid section14Catalog 6 (⟨200,(4),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2850 : RecordDataValid section14Catalog 6 (⟨200,(4),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2851 : RecordDataValid section14Catalog 6 (⟨200,(5),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2852 : RecordDataValid section14Catalog 6 (⟨200,(5),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2853 : RecordDataValid section14Catalog 6 (⟨200,(6),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2854 : RecordDataValid section14Catalog 6 (⟨200,(6),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2855 : RecordDataValid section14Catalog 6 (⟨200,(7),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2856 : RecordDataValid section14Catalog 6 (⟨200,(7),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2857 : RecordDataValid section14Catalog 6 (⟨200,(8),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2858 : RecordDataValid section14Catalog 6 (⟨200,(8),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2859 : RecordDataValid section14Catalog 6 (⟨200,(9),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2860 : RecordDataValid section14Catalog 6 (⟨200,(9),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2861 : RecordDataValid section14Catalog 6 (⟨200,(10),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2862 : RecordDataValid section14Catalog 6 (⟨200,(10),[5,6],[174],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2863 : RecordDataValid section14Catalog 6 (⟨200,(11),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2864 : RecordDataValid section14Catalog 6 (⟨200,(11),[5,6],[174],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2865 : RecordDataValid section14Catalog 6 (⟨200,(12),[1,2,5,6,13,14],[170],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2866 : RecordDataValid section14Catalog 6 (⟨200,(12),[5,6],[174],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2867 : RecordDataValid section14Catalog 6 (⟨200,(13),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2868 : RecordDataValid section14Catalog 6 (⟨200,(13),[5,6],[174],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2869 : RecordDataValid section14Catalog 6 (⟨200,(14),[1,2,5,6,13,14],[170],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2870 : RecordDataValid section14Catalog 6 (⟨200,(14),[5,6],[174],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2871 : RecordDataValid section14Catalog 6 (⟨200,(15),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2872 : RecordDataValid section14Catalog 6 (⟨200,(15),[5,6],[174],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2873 : RecordDataValid section14Catalog 6 (⟨200,(16),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2874 : RecordDataValid section14Catalog 6 (⟨200,(16),[5,6],[174],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2875 : RecordDataValid section14Catalog 6 (⟨200,(17),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2876 : RecordDataValid section14Catalog 6 (⟨200,(17),[5,6],[174],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2877 : RecordDataValid section14Catalog 6 (⟨200,(18),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2878 : RecordDataValid section14Catalog 6 (⟨200,(18),[5,6],[174],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2879 : RecordDataValid section14Catalog 6 (⟨200,(19),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2848_2880 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2848).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2848).take 32 = [⟨200,(3),[5,6],[174],704⟩,⟨200,(4),[1,2,5,6,13,14],[170],704⟩,⟨200,(4),[5,6],[174],704⟩,⟨200,(5),[1,2,5,6,13,14],[170],705⟩,⟨200,(5),[5,6],[174],705⟩,⟨200,(6),[1,2,5,6,13,14],[170],705⟩,⟨200,(6),[5,6],[174],705⟩,⟨200,(7),[1,2,5,6,13,14],[170],705⟩,⟨200,(7),[5,6],[174],705⟩,⟨200,(8),[1,2,5,6,13,14],[170],705⟩,⟨200,(8),[5,6],[174],705⟩,⟨200,(9),[1,2,5,6,13,14],[170],705⟩,⟨200,(9),[5,6],[174],705⟩,⟨200,(10),[1,2,5,6,13,14],[170],706⟩,⟨200,(10),[5,6],[174],706⟩,⟨200,(11),[1,2,5,6,13,14],[170],707⟩,⟨200,(11),[5,6],[174],707⟩,⟨200,(12),[1,2,5,6,13,14],[170],708⟩,⟨200,(12),[5,6],[174],708⟩,⟨200,(13),[1,2,5,6,13,14],[170],707⟩,⟨200,(13),[5,6],[174],707⟩,⟨200,(14),[1,2,5,6,13,14],[170],709⟩,⟨200,(14),[5,6],[174],709⟩,⟨200,(15),[1,2,5,6,13,14],[170],706⟩,⟨200,(15),[5,6],[174],706⟩,⟨200,(16),[1,2,5,6,13,14],[170],710⟩,⟨200,(16),[5,6],[174],710⟩,⟨200,(17),[1,2,5,6,13,14],[170],710⟩,⟨200,(17),[5,6],[174],710⟩,⟨200,(18),[1,2,5,6,13,14],[170],710⟩,⟨200,(18),[5,6],[174],710⟩,⟨200,(19),[1,2,5,6,13,14],[170],710⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2848
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2849
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2850
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2851
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2852
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2853
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2854
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2855
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2856
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2857
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2858
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2859
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2860
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2861
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2862
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2863
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2864
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2865
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2866
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2867
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2868
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2869
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2870
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2871
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2872
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2873
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2874
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2875
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2876
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2877
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2878
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2879
end Section14Records_6_2848_2880

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2848_2880

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2816).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2816 2848 2880 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2816_2848 hnum) (Freiman.workReverse20260919_s0006_records_2848_2880 hnum))

#print axioms solution
