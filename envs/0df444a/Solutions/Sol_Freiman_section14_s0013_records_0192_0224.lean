-- Prove2me | solution 1 for Freiman.section14_s0013_records_0192_0224
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T11:42:47.614102+00:00
-- url     : https://prove2.me/submissions/7581a3ed-14e3-4d99-93d9-ff3ea2277d64

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
namespace Section14Records_13_192_224
private theorem valid192 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid193 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid194 : RecordDataValid section14Catalog 13 (⟨18,(5),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid195 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid196 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid197 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid198 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid199 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid200 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid201 : RecordDataValid section14Catalog 13 (⟨18,(6),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid202 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid203 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid204 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid205 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid206 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid207 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid208 : RecordDataValid section14Catalog 13 (⟨18,(7),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid209 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid210 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid211 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid212 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid213 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid214 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid215 : RecordDataValid section14Catalog 13 (⟨18,(8),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid216 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,2,5,6,13,14],[131],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid217 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,2,5,6,13,14],[150],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid218 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid219 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,5,13],[135],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid220 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,13],[146],74⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨74,[1,5,9,13],74⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid221 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,13],[151],126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨126,[1,2,3,5,6,7,13,14,15],126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid222 : RecordDataValid section14Catalog 13 (⟨18,(9),[1,13],[147],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid223 : RecordDataValid section14Catalog 13 (⟨18,(10),[1,2,5,6,13,14],[131],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 192).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 192).take 32 = [⟨18,(5),[1,13],[146],74⟩,⟨18,(5),[1,13],[151],126⟩,⟨18,(5),[1,13],[147],161⟩,⟨18,(6),[1,2,5,6,13,14],[131],107⟩,⟨18,(6),[1,2,5,6,13,14],[150],126⟩,⟨18,(6),[1,2,13,14],[190],3⟩,⟨18,(6),[1,5,13],[135],126⟩,⟨18,(6),[1,13],[146],74⟩,⟨18,(6),[1,13],[151],126⟩,⟨18,(6),[1,13],[147],161⟩,⟨18,(7),[1,2,5,6,13,14],[131],107⟩,⟨18,(7),[1,2,5,6,13,14],[150],126⟩,⟨18,(7),[1,2,13,14],[190],3⟩,⟨18,(7),[1,5,13],[135],126⟩,⟨18,(7),[1,13],[146],74⟩,⟨18,(7),[1,13],[151],126⟩,⟨18,(7),[1,13],[147],161⟩,⟨18,(8),[1,2,5,6,13,14],[131],107⟩,⟨18,(8),[1,2,5,6,13,14],[150],126⟩,⟨18,(8),[1,2,13,14],[190],3⟩,⟨18,(8),[1,5,13],[135],126⟩,⟨18,(8),[1,13],[146],74⟩,⟨18,(8),[1,13],[151],126⟩,⟨18,(8),[1,13],[147],161⟩,⟨18,(9),[1,2,5,6,13,14],[131],107⟩,⟨18,(9),[1,2,5,6,13,14],[150],126⟩,⟨18,(9),[1,2,13,14],[190],3⟩,⟨18,(9),[1,5,13],[135],126⟩,⟨18,(9),[1,13],[146],74⟩,⟨18,(9),[1,13],[151],126⟩,⟨18,(9),[1,13],[147],161⟩,⟨18,(10),[1,2,5,6,13,14],[131],108⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid192
  · exact recordValid_of_data section14Catalog 13 _ hnum valid193
  · exact recordValid_of_data section14Catalog 13 _ hnum valid194
  · exact recordValid_of_data section14Catalog 13 _ hnum valid195
  · exact recordValid_of_data section14Catalog 13 _ hnum valid196
  · exact recordValid_of_data section14Catalog 13 _ hnum valid197
  · exact recordValid_of_data section14Catalog 13 _ hnum valid198
  · exact recordValid_of_data section14Catalog 13 _ hnum valid199
  · exact recordValid_of_data section14Catalog 13 _ hnum valid200
  · exact recordValid_of_data section14Catalog 13 _ hnum valid201
  · exact recordValid_of_data section14Catalog 13 _ hnum valid202
  · exact recordValid_of_data section14Catalog 13 _ hnum valid203
  · exact recordValid_of_data section14Catalog 13 _ hnum valid204
  · exact recordValid_of_data section14Catalog 13 _ hnum valid205
  · exact recordValid_of_data section14Catalog 13 _ hnum valid206
  · exact recordValid_of_data section14Catalog 13 _ hnum valid207
  · exact recordValid_of_data section14Catalog 13 _ hnum valid208
  · exact recordValid_of_data section14Catalog 13 _ hnum valid209
  · exact recordValid_of_data section14Catalog 13 _ hnum valid210
  · exact recordValid_of_data section14Catalog 13 _ hnum valid211
  · exact recordValid_of_data section14Catalog 13 _ hnum valid212
  · exact recordValid_of_data section14Catalog 13 _ hnum valid213
  · exact recordValid_of_data section14Catalog 13 _ hnum valid214
  · exact recordValid_of_data section14Catalog 13 _ hnum valid215
  · exact recordValid_of_data section14Catalog 13 _ hnum valid216
  · exact recordValid_of_data section14Catalog 13 _ hnum valid217
  · exact recordValid_of_data section14Catalog 13 _ hnum valid218
  · exact recordValid_of_data section14Catalog 13 _ hnum valid219
  · exact recordValid_of_data section14Catalog 13 _ hnum valid220
  · exact recordValid_of_data section14Catalog 13 _ hnum valid221
  · exact recordValid_of_data section14Catalog 13 _ hnum valid222
  · exact recordValid_of_data section14Catalog 13 _ hnum valid223
end Section14Records_13_192_224

#print axioms solution
