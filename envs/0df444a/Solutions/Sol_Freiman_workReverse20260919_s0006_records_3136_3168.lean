-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3136_3168
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:45:15.644132+00:00
-- url     : https://prove2.me/submissions/3073cd36-2b40-46af-a020-4643171eacdf

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
namespace Section14Records_6_3136_3168
private theorem valid3136 : RecordDataValid section14Catalog 6 (⟨215,(15),[5,6],[174],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3137 : RecordDataValid section14Catalog 6 (⟨218,(0),[1,2,5,6],[170],506⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨506,[1,2,3,4,5,6,7,8,9,10,11,12],507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3138 : RecordDataValid section14Catalog 6 (⟨218,(0),[5,6],[174],307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨307,[1,2,3,5,6,7],308⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3139 : RecordDataValid section14Catalog 6 (⟨218,(1),[1,2,5,6],[170],507⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨507,[1,2,3,4,5,6,7,8,9,10,11,12],508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3140 : RecordDataValid section14Catalog 6 (⟨218,(1),[5,6],[174],308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨308,[1,2,3,5,6,7],309⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3141 : RecordDataValid section14Catalog 6 (⟨218,(2),[1,2,5,6],[170],508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨508,[1,2,3,4,5,6,7,8,9,10,11,12],509⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3142 : RecordDataValid section14Catalog 6 (⟨218,(2),[5,6],[174],309⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨309,[1,2,3,5,6,7],310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3143 : RecordDataValid section14Catalog 6 (⟨218,(3),[1,2,5,6],[170],509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨509,[1,2,3,4,5,6,7,8,9,10,11,12],510⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3144 : RecordDataValid section14Catalog 6 (⟨218,(3),[5,6],[174],310⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨310,[1,2,3,5,6,7],311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3145 : RecordDataValid section14Catalog 6 (⟨220,(0),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3146 : RecordDataValid section14Catalog 6 (⟨220,(0),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3147 : RecordDataValid section14Catalog 6 (⟨220,(1),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3148 : RecordDataValid section14Catalog 6 (⟨220,(1),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3149 : RecordDataValid section14Catalog 6 (⟨220,(2),[1,2,5,6,13,14],[170],734⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨734,[1,2,5,6,9,10,13,14],735⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3150 : RecordDataValid section14Catalog 6 (⟨220,(2),[5,6],[174],734⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨734,[1,2,5,6,9,10,13,14],735⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3151 : RecordDataValid section14Catalog 6 (⟨220,(3),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3152 : RecordDataValid section14Catalog 6 (⟨220,(3),[5,6],[174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3153 : RecordDataValid section14Catalog 6 (⟨220,(4),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3154 : RecordDataValid section14Catalog 6 (⟨220,(4),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3155 : RecordDataValid section14Catalog 6 (⟨220,(5),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3156 : RecordDataValid section14Catalog 6 (⟨220,(5),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3157 : RecordDataValid section14Catalog 6 (⟨220,(6),[1,2,5,6,13,14],[170],511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨511,[1,2,5,6,9,10,13,14],512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3158 : RecordDataValid section14Catalog 6 (⟨220,(6),[5,6],[174],511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨511,[1,2,5,6,9,10,13,14],512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3159 : RecordDataValid section14Catalog 6 (⟨220,(7),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3160 : RecordDataValid section14Catalog 6 (⟨220,(7),[5,6],[174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3161 : RecordDataValid section14Catalog 6 (⟨220,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3162 : RecordDataValid section14Catalog 6 (⟨220,(8),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3163 : RecordDataValid section14Catalog 6 (⟨220,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3164 : RecordDataValid section14Catalog 6 (⟨220,(9),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3165 : RecordDataValid section14Catalog 6 (⟨220,(10),[1,2,5,6,13,14],[170],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3166 : RecordDataValid section14Catalog 6 (⟨220,(10),[5,6],[174],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3167 : RecordDataValid section14Catalog 6 (⟨220,(11),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3136).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3136).take 32 = [⟨215,(15),[5,6],[174],731⟩,⟨218,(0),[1,2,5,6],[170],506⟩,⟨218,(0),[5,6],[174],307⟩,⟨218,(1),[1,2,5,6],[170],507⟩,⟨218,(1),[5,6],[174],308⟩,⟨218,(2),[1,2,5,6],[170],508⟩,⟨218,(2),[5,6],[174],309⟩,⟨218,(3),[1,2,5,6],[170],509⟩,⟨218,(3),[5,6],[174],310⟩,⟨220,(0),[1,2,5,6,13,14],[170],3⟩,⟨220,(0),[5,6],[174],3⟩,⟨220,(1),[1,2,5,6,13,14],[170],3⟩,⟨220,(1),[5,6],[174],3⟩,⟨220,(2),[1,2,5,6,13,14],[170],734⟩,⟨220,(2),[5,6],[174],734⟩,⟨220,(3),[1,2,5,6,13,14],[170],29⟩,⟨220,(3),[5,6],[174],29⟩,⟨220,(4),[1,2,5,6,13,14],[170],3⟩,⟨220,(4),[5,6],[174],3⟩,⟨220,(5),[1,2,5,6,13,14],[170],3⟩,⟨220,(5),[5,6],[174],3⟩,⟨220,(6),[1,2,5,6,13,14],[170],511⟩,⟨220,(6),[5,6],[174],511⟩,⟨220,(7),[1,2,5,6,13,14],[170],29⟩,⟨220,(7),[5,6],[174],29⟩,⟨220,(8),[1,2,5,6,13,14],[170],3⟩,⟨220,(8),[5,6],[174],3⟩,⟨220,(9),[1,2,5,6,13,14],[170],3⟩,⟨220,(9),[5,6],[174],3⟩,⟨220,(10),[1,2,5,6,13,14],[170],512⟩,⟨220,(10),[5,6],[174],512⟩,⟨220,(11),[1,2,5,6,13,14],[170],29⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3136
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3137
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3138
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3139
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3140
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3141
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3142
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3143
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3144
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3145
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3146
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3147
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3148
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3149
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3150
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3151
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3152
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3153
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3154
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3155
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3156
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3157
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3158
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3159
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3160
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3161
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3162
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3163
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3164
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3165
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3166
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3167
end Section14Records_6_3136_3168

#print axioms solution
