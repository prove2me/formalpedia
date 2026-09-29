-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3008_3072
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:30:53.177987+00:00
-- url     : https://prove2.me/submissions/24660c7a-0689-4823-bb69-650ec9a64504

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3008_3040
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3008_3040
private theorem valid3008 : RecordDataValid section14Catalog 5 (⟨190,(23),[1,2,5,6,13,14],[170],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3009 : RecordDataValid section14Catalog 5 (⟨190,(23),[5,6],[174],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3010 : RecordDataValid section14Catalog 5 (⟨190,(24),[1,2,5,6,13,14],[170],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3011 : RecordDataValid section14Catalog 5 (⟨190,(24),[5,6],[174],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3012 : RecordDataValid section14Catalog 5 (⟨192,(0),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3013 : RecordDataValid section14Catalog 5 (⟨192,(0),[5,6],[174],1001⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1001,[3,5,6,7],1005⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3014 : RecordDataValid section14Catalog 5 (⟨192,(1),[1,2,5,6,13,14],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3015 : RecordDataValid section14Catalog 5 (⟨192,(1),[5,6],[174],1002⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1002,[3,5,6,7],1006⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3016 : RecordDataValid section14Catalog 5 (⟨192,(2),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3017 : RecordDataValid section14Catalog 5 (⟨192,(2),[5,6],[174],1001⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1001,[3,5,6,7],1005⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3018 : RecordDataValid section14Catalog 5 (⟨192,(3),[1,2,5,6,13,14],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3019 : RecordDataValid section14Catalog 5 (⟨192,(3),[5,6],[174],1003⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1003,[3,5,6,7],1007⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3020 : RecordDataValid section14Catalog 5 (⟨192,(4),[1,2,5,6,13,14],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3021 : RecordDataValid section14Catalog 5 (⟨192,(4),[5,6],[174],1004⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1004,[3,5,6,7],1008⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3022 : RecordDataValid section14Catalog 5 (⟨192,(5),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3023 : RecordDataValid section14Catalog 5 (⟨192,(5),[5,6],[174],1001⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1001,[3,5,6,7],1005⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3024 : RecordDataValid section14Catalog 5 (⟨192,(6),[1,2,5,6,13,14],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3025 : RecordDataValid section14Catalog 5 (⟨192,(6),[5,6],[174],1002⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1002,[3,5,6,7],1006⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3026 : RecordDataValid section14Catalog 5 (⟨192,(7),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3027 : RecordDataValid section14Catalog 5 (⟨192,(7),[5,6],[174],1001⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1001,[3,5,6,7],1005⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3028 : RecordDataValid section14Catalog 5 (⟨192,(8),[1,2,5,6,13,14],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3029 : RecordDataValid section14Catalog 5 (⟨192,(8),[5,6],[174],1003⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1003,[3,5,6,7],1007⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3030 : RecordDataValid section14Catalog 5 (⟨192,(9),[1,2,5,6,13,14],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3031 : RecordDataValid section14Catalog 5 (⟨192,(9),[5,6],[174],1004⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1004,[3,5,6,7],1008⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3032 : RecordDataValid section14Catalog 5 (⟨192,(10),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3033 : RecordDataValid section14Catalog 5 (⟨192,(10),[5,6],[174],1005⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1005,[3,5,6,7],1009⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3034 : RecordDataValid section14Catalog 5 (⟨192,(11),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3035 : RecordDataValid section14Catalog 5 (⟨192,(11),[5,6],[174],1005⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1005,[3,5,6,7],1009⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3036 : RecordDataValid section14Catalog 5 (⟨192,(12),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3037 : RecordDataValid section14Catalog 5 (⟨192,(12),[5,6],[174],1005⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1005,[3,5,6,7],1009⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3038 : RecordDataValid section14Catalog 5 (⟨192,(13),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3039 : RecordDataValid section14Catalog 5 (⟨192,(13),[5,6],[174],1005⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1005,[3,5,6,7],1009⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3008_3040 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3008).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3008).take 32 = [⟨190,(23),[1,2,5,6,13,14],[170],693⟩,⟨190,(23),[5,6],[174],693⟩,⟨190,(24),[1,2,5,6,13,14],[170],695⟩,⟨190,(24),[5,6],[174],695⟩,⟨192,(0),[1,2,5,6,13,14],[170],441⟩,⟨192,(0),[5,6],[174],1001⟩,⟨192,(1),[1,2,5,6,13,14],[170],442⟩,⟨192,(1),[5,6],[174],1002⟩,⟨192,(2),[1,2,5,6,13,14],[170],441⟩,⟨192,(2),[5,6],[174],1001⟩,⟨192,(3),[1,2,5,6,13,14],[170],443⟩,⟨192,(3),[5,6],[174],1003⟩,⟨192,(4),[1,2,5,6,13,14],[170],444⟩,⟨192,(4),[5,6],[174],1004⟩,⟨192,(5),[1,2,5,6,13,14],[170],441⟩,⟨192,(5),[5,6],[174],1001⟩,⟨192,(6),[1,2,5,6,13,14],[170],442⟩,⟨192,(6),[5,6],[174],1002⟩,⟨192,(7),[1,2,5,6,13,14],[170],441⟩,⟨192,(7),[5,6],[174],1001⟩,⟨192,(8),[1,2,5,6,13,14],[170],443⟩,⟨192,(8),[5,6],[174],1003⟩,⟨192,(9),[1,2,5,6,13,14],[170],444⟩,⟨192,(9),[5,6],[174],1004⟩,⟨192,(10),[1,2,5,6,13,14],[170],445⟩,⟨192,(10),[5,6],[174],1005⟩,⟨192,(11),[1,2,5,6,13,14],[170],445⟩,⟨192,(11),[5,6],[174],1005⟩,⟨192,(12),[1,2,5,6,13,14],[170],445⟩,⟨192,(12),[5,6],[174],1005⟩,⟨192,(13),[1,2,5,6,13,14],[170],445⟩,⟨192,(13),[5,6],[174],1005⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3008
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3009
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3010
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3011
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3012
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3013
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3014
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3015
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3016
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3017
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3018
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3019
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3020
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3021
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3022
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3023
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3024
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3025
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3026
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3027
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3028
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3029
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3030
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3031
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3032
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3033
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3034
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3035
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3036
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3037
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3038
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3039
end Section14Records_5_3008_3040

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3008_3040


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3040_3072
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3040_3072
private theorem valid3040 : RecordDataValid section14Catalog 5 (⟨192,(14),[1,2,5,6,13,14],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3041 : RecordDataValid section14Catalog 5 (⟨192,(14),[5,6],[174],1004⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1004,[3,5,6,7],1008⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3042 : RecordDataValid section14Catalog 5 (⟨192,(15),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3043 : RecordDataValid section14Catalog 5 (⟨192,(15),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3044 : RecordDataValid section14Catalog 5 (⟨192,(16),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3045 : RecordDataValid section14Catalog 5 (⟨192,(16),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3046 : RecordDataValid section14Catalog 5 (⟨192,(17),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3047 : RecordDataValid section14Catalog 5 (⟨192,(17),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3048 : RecordDataValid section14Catalog 5 (⟨192,(18),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3049 : RecordDataValid section14Catalog 5 (⟨192,(18),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3050 : RecordDataValid section14Catalog 5 (⟨192,(19),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3051 : RecordDataValid section14Catalog 5 (⟨192,(19),[5,6],[174],1006⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1006,[3,5,6,7],1010⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3052 : RecordDataValid section14Catalog 5 (⟨192,(20),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3053 : RecordDataValid section14Catalog 5 (⟨192,(20),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3054 : RecordDataValid section14Catalog 5 (⟨192,(21),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3055 : RecordDataValid section14Catalog 5 (⟨192,(21),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3056 : RecordDataValid section14Catalog 5 (⟨192,(22),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3057 : RecordDataValid section14Catalog 5 (⟨192,(22),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3058 : RecordDataValid section14Catalog 5 (⟨192,(23),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3059 : RecordDataValid section14Catalog 5 (⟨192,(23),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3060 : RecordDataValid section14Catalog 5 (⟨192,(24),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3061 : RecordDataValid section14Catalog 5 (⟨192,(24),[5,6],[174],1007⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1007,[3,5,6,7],1011⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3062 : RecordDataValid section14Catalog 5 (⟨195,(0),[1,2,5,6,13,14],[170],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3063 : RecordDataValid section14Catalog 5 (⟨195,(0),[5,6],[174],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3064 : RecordDataValid section14Catalog 5 (⟨195,(1),[1,2,5,6,13,14],[170],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3065 : RecordDataValid section14Catalog 5 (⟨195,(1),[5,6],[174],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3066 : RecordDataValid section14Catalog 5 (⟨195,(2),[1,2,5,6,13,14],[170],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3067 : RecordDataValid section14Catalog 5 (⟨195,(2),[5,6],[174],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3068 : RecordDataValid section14Catalog 5 (⟨195,(3),[1,2,5,6,13,14],[170],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3069 : RecordDataValid section14Catalog 5 (⟨195,(3),[5,6],[174],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3070 : RecordDataValid section14Catalog 5 (⟨195,(4),[1,2,5,6,13,14],[170],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3071 : RecordDataValid section14Catalog 5 (⟨195,(4),[5,6],[174],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3040_3072 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3040).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3040).take 32 = [⟨192,(14),[1,2,5,6,13,14],[170],444⟩,⟨192,(14),[5,6],[174],1004⟩,⟨192,(15),[1,2,5,6,13,14],[170],446⟩,⟨192,(15),[5,6],[174],1006⟩,⟨192,(16),[1,2,5,6,13,14],[170],446⟩,⟨192,(16),[5,6],[174],1006⟩,⟨192,(17),[1,2,5,6,13,14],[170],446⟩,⟨192,(17),[5,6],[174],1006⟩,⟨192,(18),[1,2,5,6,13,14],[170],446⟩,⟨192,(18),[5,6],[174],1006⟩,⟨192,(19),[1,2,5,6,13,14],[170],446⟩,⟨192,(19),[5,6],[174],1006⟩,⟨192,(20),[1,2,5,6,13,14],[170],447⟩,⟨192,(20),[5,6],[174],1007⟩,⟨192,(21),[1,2,5,6,13,14],[170],447⟩,⟨192,(21),[5,6],[174],1007⟩,⟨192,(22),[1,2,5,6,13,14],[170],447⟩,⟨192,(22),[5,6],[174],1007⟩,⟨192,(23),[1,2,5,6,13,14],[170],447⟩,⟨192,(23),[5,6],[174],1007⟩,⟨192,(24),[1,2,5,6,13,14],[170],447⟩,⟨192,(24),[5,6],[174],1007⟩,⟨195,(0),[1,2,5,6,13,14],[170],697⟩,⟨195,(0),[5,6],[174],697⟩,⟨195,(1),[1,2,5,6,13,14],[170],697⟩,⟨195,(1),[5,6],[174],697⟩,⟨195,(2),[1,2,5,6,13,14],[170],698⟩,⟨195,(2),[5,6],[174],698⟩,⟨195,(3),[1,2,5,6,13,14],[170],698⟩,⟨195,(3),[5,6],[174],698⟩,⟨195,(4),[1,2,5,6,13,14],[170],699⟩,⟨195,(4),[5,6],[174],699⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3040
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3041
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3042
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3043
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3044
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3045
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3046
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3047
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3048
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3049
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3050
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3051
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3052
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3053
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3054
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3055
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3056
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3057
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3058
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3059
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3060
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3061
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3062
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3063
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3064
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3065
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3066
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3067
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3068
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3069
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3070
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3071
end Section14Records_5_3040_3072

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3040_3072

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3008).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 3008 3040 3072 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_3008_3040 hnum) (Freiman.workReverse20260919_s0005_records_3040_3072 hnum))

#print axioms solution
