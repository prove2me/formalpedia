-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3072_3104
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:43:37.949817+00:00
-- url     : https://prove2.me/submissions/b00a974a-9d8c-4b2c-8e65-9ef254a704fc

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
namespace Section14Records_6_3072_3104
private theorem valid3072 : RecordDataValid section14Catalog 6 (⟨210,(15),[5,6],[174],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3073 : RecordDataValid section14Catalog 6 (⟨213,(0),[1,2,5,6,13,14],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3074 : RecordDataValid section14Catalog 6 (⟨213,(0),[5,6],[174],1029⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1029,[3,5,6,7],1033⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3075 : RecordDataValid section14Catalog 6 (⟨213,(1),[1,2,5,6,13,14],[170],495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨495,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3076 : RecordDataValid section14Catalog 6 (⟨213,(1),[5,6],[174],1030⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1030,[3,5,6,7],1034⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3077 : RecordDataValid section14Catalog 6 (⟨213,(2),[1,2,5,6,13,14],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3078 : RecordDataValid section14Catalog 6 (⟨213,(2),[5,6],[174],1029⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1029,[3,5,6,7],1033⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3079 : RecordDataValid section14Catalog 6 (⟨213,(3),[1,2,5,6,13,14],[170],496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨496,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3080 : RecordDataValid section14Catalog 6 (⟨213,(3),[5,6],[174],1031⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1031,[3,5,6,7],1035⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3081 : RecordDataValid section14Catalog 6 (⟨213,(4),[1,2,5,6,13,14],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3082 : RecordDataValid section14Catalog 6 (⟨213,(4),[5,6],[174],1032⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1032,[3,5,6,7],1036⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3083 : RecordDataValid section14Catalog 6 (⟨213,(5),[1,2,5,6,13,14],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3084 : RecordDataValid section14Catalog 6 (⟨213,(5),[5,6],[174],1032⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1032,[3,5,6,7],1036⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3085 : RecordDataValid section14Catalog 6 (⟨213,(6),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3086 : RecordDataValid section14Catalog 6 (⟨213,(6),[5,6],[174],1032⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1032,[3,5,6,7],1036⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3087 : RecordDataValid section14Catalog 6 (⟨213,(7),[1,2,5,6,13,14],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3088 : RecordDataValid section14Catalog 6 (⟨213,(7),[5,6],[174],1032⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1032,[3,5,6,7],1036⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3089 : RecordDataValid section14Catalog 6 (⟨213,(8),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3090 : RecordDataValid section14Catalog 6 (⟨213,(8),[5,6],[174],1034⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1034,[3,5,6,7],1038⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3091 : RecordDataValid section14Catalog 6 (⟨213,(9),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3092 : RecordDataValid section14Catalog 6 (⟨213,(9),[5,6],[174],1034⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1034,[3,5,6,7],1038⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3093 : RecordDataValid section14Catalog 6 (⟨213,(10),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3094 : RecordDataValid section14Catalog 6 (⟨213,(10),[5,6],[174],1034⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1034,[3,5,6,7],1038⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3095 : RecordDataValid section14Catalog 6 (⟨213,(11),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3096 : RecordDataValid section14Catalog 6 (⟨213,(11),[5,6],[174],1034⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1034,[3,5,6,7],1038⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3097 : RecordDataValid section14Catalog 6 (⟨213,(12),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3098 : RecordDataValid section14Catalog 6 (⟨213,(12),[5,6],[174],1035⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1035,[3,5,6,7],1039⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3099 : RecordDataValid section14Catalog 6 (⟨213,(13),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3100 : RecordDataValid section14Catalog 6 (⟨213,(13),[5,6],[174],1035⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1035,[3,5,6,7],1039⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3101 : RecordDataValid section14Catalog 6 (⟨213,(14),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3102 : RecordDataValid section14Catalog 6 (⟨213,(14),[5,6],[174],1035⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1035,[3,5,6,7],1039⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3103 : RecordDataValid section14Catalog 6 (⟨213,(15),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3072).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3072).take 32 = [⟨210,(15),[5,6],[174],725⟩,⟨213,(0),[1,2,5,6,13,14],[170],494⟩,⟨213,(0),[5,6],[174],1029⟩,⟨213,(1),[1,2,5,6,13,14],[170],495⟩,⟨213,(1),[5,6],[174],1030⟩,⟨213,(2),[1,2,5,6,13,14],[170],494⟩,⟨213,(2),[5,6],[174],1029⟩,⟨213,(3),[1,2,5,6,13,14],[170],496⟩,⟨213,(3),[5,6],[174],1031⟩,⟨213,(4),[1,2,5,6,13,14],[170],497⟩,⟨213,(4),[5,6],[174],1032⟩,⟨213,(5),[1,2,5,6,13,14],[170],497⟩,⟨213,(5),[5,6],[174],1032⟩,⟨213,(6),[1,5,6,13],[170],497⟩,⟨213,(6),[5,6],[174],1032⟩,⟨213,(7),[1,2,5,6,13,14],[170],497⟩,⟨213,(7),[5,6],[174],1032⟩,⟨213,(8),[1,2,5,6,13,14],[170],498⟩,⟨213,(8),[5,6],[174],1034⟩,⟨213,(9),[1,2,5,6,13,14],[170],498⟩,⟨213,(9),[5,6],[174],1034⟩,⟨213,(10),[1,2,5,6,13,14],[170],498⟩,⟨213,(10),[5,6],[174],1034⟩,⟨213,(11),[1,2,5,6,13,14],[170],498⟩,⟨213,(11),[5,6],[174],1034⟩,⟨213,(12),[1,2,5,6,13,14],[170],499⟩,⟨213,(12),[5,6],[174],1035⟩,⟨213,(13),[1,2,5,6,13,14],[170],499⟩,⟨213,(13),[5,6],[174],1035⟩,⟨213,(14),[1,2,5,6,13,14],[170],499⟩,⟨213,(14),[5,6],[174],1035⟩,⟨213,(15),[1,2,5,6,13,14],[170],499⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3072
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3073
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3074
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3075
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3076
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3077
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3078
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3079
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3080
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3081
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3082
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3083
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3084
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3085
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3086
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3087
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3088
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3089
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3090
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3091
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3092
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3093
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3094
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3095
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3096
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3097
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3098
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3099
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3100
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3101
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3102
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3103
end Section14Records_6_3072_3104

#print axioms solution
