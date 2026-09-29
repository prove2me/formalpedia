-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_0800_0832
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:14:38.461576+00:00
-- url     : https://prove2.me/submissions/a4042439-62d9-4787-960c-64ad24765fd5

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
namespace Section14Records_13_800_832
private theorem valid800 : RecordDataValid section14Catalog 13 (⟨33,(13),[13,14],[131],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid801 : RecordDataValid section14Catalog 13 (⟨33,(14),[1,2,13],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid802 : RecordDataValid section14Catalog 13 (⟨33,(14),[6,13],[131,146,150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid803 : RecordDataValid section14Catalog 13 (⟨33,(14),[13],[135,147,151],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid804 : RecordDataValid section14Catalog 13 (⟨33,(15),[1,2,13,14],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid805 : RecordDataValid section14Catalog 13 (⟨33,(15),[6,13],[131,146,150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid806 : RecordDataValid section14Catalog 13 (⟨33,(15),[13],[135,147,151],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid807 : RecordDataValid section14Catalog 13 (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid808 : RecordDataValid section14Catalog 13 (⟨36,(5),[1,2,13,14],[147],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid809 : RecordDataValid section14Catalog 13 (⟨36,(5),[1,5,13],[135],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid810 : RecordDataValid section14Catalog 13 (⟨36,(5),[1,13],[151],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid811 : RecordDataValid section14Catalog 13 (⟨36,(5),[13],[190],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid812 : RecordDataValid section14Catalog 13 (⟨36,(7),[1,2,5,6,13,14],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid813 : RecordDataValid section14Catalog 13 (⟨36,(7),[1,5,13],[135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid814 : RecordDataValid section14Catalog 13 (⟨36,(7),[1,13],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid815 : RecordDataValid section14Catalog 13 (⟨36,(7),[13],[190],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid816 : RecordDataValid section14Catalog 13 (⟨36,(7),[13],[131,146,147],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid817 : RecordDataValid section14Catalog 13 (⟨36,(8),[1,2,5,6,13,14],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid818 : RecordDataValid section14Catalog 13 (⟨36,(8),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid819 : RecordDataValid section14Catalog 13 (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid820 : RecordDataValid section14Catalog 13 (⟨36,(8),[1,5,13],[135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid821 : RecordDataValid section14Catalog 13 (⟨36,(8),[1,13],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid822 : RecordDataValid section14Catalog 13 (⟨36,(8),[1,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid823 : RecordDataValid section14Catalog 13 (⟨36,(9),[1,2,5,6,13,14],[150],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid824 : RecordDataValid section14Catalog 13 (⟨36,(9),[1,5,13],[135],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid825 : RecordDataValid section14Catalog 13 (⟨36,(9),[1,13],[131,146,147],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid826 : RecordDataValid section14Catalog 13 (⟨36,(9),[1,13],[151],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid827 : RecordDataValid section14Catalog 13 (⟨36,(9),[13,14],[190],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid828 : RecordDataValid section14Catalog 13 (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid829 : RecordDataValid section14Catalog 13 (⟨36,(15),[1,2,13,14],[147,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid830 : RecordDataValid section14Catalog 13 (⟨36,(15),[13],[135,150,151],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid831 : RecordDataValid section14Catalog 13 (⟨36,(16),[1,2,5,6,13,14],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 800).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 800).take 32 = [⟨33,(13),[13,14],[131],98⟩,⟨33,(14),[1,2,13],[190],99⟩,⟨33,(14),[6,13],[131,146,150],99⟩,⟨33,(14),[13],[135,147,151],99⟩,⟨33,(15),[1,2,13,14],[190],99⟩,⟨33,(15),[6,13],[131,146,150],99⟩,⟨33,(15),[13],[135,147,151],99⟩,⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩,⟨36,(5),[1,2,13,14],[147],105⟩,⟨36,(5),[1,5,13],[135],105⟩,⟨36,(5),[1,13],[151],105⟩,⟨36,(5),[13],[190],105⟩,⟨36,(7),[1,2,5,6,13,14],[150],3⟩,⟨36,(7),[1,5,13],[135],3⟩,⟨36,(7),[1,13],[151],3⟩,⟨36,(7),[13],[190],48⟩,⟨36,(7),[13],[131,146,147],105⟩,⟨36,(8),[1,2,5,6,13,14],[150],3⟩,⟨36,(8),[1,2,13,14],[190],3⟩,⟨36,(8),[1,5,6,13,14],[131,146],3⟩,⟨36,(8),[1,5,13],[135],3⟩,⟨36,(8),[1,13],[151],3⟩,⟨36,(8),[1,13,14],[147],3⟩,⟨36,(9),[1,2,5,6,13,14],[150],143⟩,⟨36,(9),[1,5,13],[135],143⟩,⟨36,(9),[1,13],[131,146,147],105⟩,⟨36,(9),[1,13],[151],143⟩,⟨36,(9),[13,14],[190],143⟩,⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩,⟨36,(15),[1,2,13,14],[147,190],3⟩,⟨36,(15),[13],[135,150,151],105⟩,⟨36,(16),[1,2,5,6,13,14],[150],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid800
  · exact recordValid_of_data section14Catalog 13 _ hnum valid801
  · exact recordValid_of_data section14Catalog 13 _ hnum valid802
  · exact recordValid_of_data section14Catalog 13 _ hnum valid803
  · exact recordValid_of_data section14Catalog 13 _ hnum valid804
  · exact recordValid_of_data section14Catalog 13 _ hnum valid805
  · exact recordValid_of_data section14Catalog 13 _ hnum valid806
  · exact recordValid_of_data section14Catalog 13 _ hnum valid807
  · exact recordValid_of_data section14Catalog 13 _ hnum valid808
  · exact recordValid_of_data section14Catalog 13 _ hnum valid809
  · exact recordValid_of_data section14Catalog 13 _ hnum valid810
  · exact recordValid_of_data section14Catalog 13 _ hnum valid811
  · exact recordValid_of_data section14Catalog 13 _ hnum valid812
  · exact recordValid_of_data section14Catalog 13 _ hnum valid813
  · exact recordValid_of_data section14Catalog 13 _ hnum valid814
  · exact recordValid_of_data section14Catalog 13 _ hnum valid815
  · exact recordValid_of_data section14Catalog 13 _ hnum valid816
  · exact recordValid_of_data section14Catalog 13 _ hnum valid817
  · exact recordValid_of_data section14Catalog 13 _ hnum valid818
  · exact recordValid_of_data section14Catalog 13 _ hnum valid819
  · exact recordValid_of_data section14Catalog 13 _ hnum valid820
  · exact recordValid_of_data section14Catalog 13 _ hnum valid821
  · exact recordValid_of_data section14Catalog 13 _ hnum valid822
  · exact recordValid_of_data section14Catalog 13 _ hnum valid823
  · exact recordValid_of_data section14Catalog 13 _ hnum valid824
  · exact recordValid_of_data section14Catalog 13 _ hnum valid825
  · exact recordValid_of_data section14Catalog 13 _ hnum valid826
  · exact recordValid_of_data section14Catalog 13 _ hnum valid827
  · exact recordValid_of_data section14Catalog 13 _ hnum valid828
  · exact recordValid_of_data section14Catalog 13 _ hnum valid829
  · exact recordValid_of_data section14Catalog 13 _ hnum valid830
  · exact recordValid_of_data section14Catalog 13 _ hnum valid831
end Section14Records_13_800_832

#print axioms solution
