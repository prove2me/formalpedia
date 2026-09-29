-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3200_3232
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:55:55.981972+00:00
-- url     : https://prove2.me/submissions/116465b2-cfae-4271-988f-bb0a0909e183

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
namespace Section14Records_5_3200_3232
private theorem valid3200 : RecordDataValid section14Catalog 5 (⟨202,(9),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3201 : RecordDataValid section14Catalog 5 (⟨202,(9),[5,6],[174],1018⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1018,[3,5,6,7],1022⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3202 : RecordDataValid section14Catalog 5 (⟨202,(10),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3203 : RecordDataValid section14Catalog 5 (⟨202,(10),[5,6],[174],1019⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1019,[3,5,6,7],1023⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3204 : RecordDataValid section14Catalog 5 (⟨202,(11),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3205 : RecordDataValid section14Catalog 5 (⟨202,(11),[5,6],[174],1019⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1019,[3,5,6,7],1023⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3206 : RecordDataValid section14Catalog 5 (⟨202,(12),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3207 : RecordDataValid section14Catalog 5 (⟨202,(12),[5,6],[174],1019⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1019,[3,5,6,7],1023⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3208 : RecordDataValid section14Catalog 5 (⟨202,(13),[1,2,5,6,13,14],[170],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3209 : RecordDataValid section14Catalog 5 (⟨202,(13),[5,6],[174],1019⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1019,[3,5,6,7],1023⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3210 : RecordDataValid section14Catalog 5 (⟨202,(14),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3211 : RecordDataValid section14Catalog 5 (⟨202,(14),[5,6],[174],1018⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1018,[3,5,6,7],1022⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3212 : RecordDataValid section14Catalog 5 (⟨202,(15),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3213 : RecordDataValid section14Catalog 5 (⟨202,(15),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3214 : RecordDataValid section14Catalog 5 (⟨202,(16),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3215 : RecordDataValid section14Catalog 5 (⟨202,(16),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3216 : RecordDataValid section14Catalog 5 (⟨202,(17),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3217 : RecordDataValid section14Catalog 5 (⟨202,(17),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3218 : RecordDataValid section14Catalog 5 (⟨202,(18),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3219 : RecordDataValid section14Catalog 5 (⟨202,(18),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3220 : RecordDataValid section14Catalog 5 (⟨202,(19),[1,2,5,6,13,14],[170],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3221 : RecordDataValid section14Catalog 5 (⟨202,(19),[5,6],[174],1020⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1020,[3,5,6,7],1024⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3222 : RecordDataValid section14Catalog 5 (⟨202,(20),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3223 : RecordDataValid section14Catalog 5 (⟨202,(20),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3224 : RecordDataValid section14Catalog 5 (⟨202,(21),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3225 : RecordDataValid section14Catalog 5 (⟨202,(21),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3226 : RecordDataValid section14Catalog 5 (⟨202,(22),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3227 : RecordDataValid section14Catalog 5 (⟨202,(22),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3228 : RecordDataValid section14Catalog 5 (⟨202,(23),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3229 : RecordDataValid section14Catalog 5 (⟨202,(23),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3230 : RecordDataValid section14Catalog 5 (⟨202,(24),[1,2,5,6,13,14],[170],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3231 : RecordDataValid section14Catalog 5 (⟨202,(24),[5,6],[174],1021⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1021,[3,5,6,7],1025⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3200).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3200).take 32 = [⟨202,(9),[1,2,5,6,13,14],[170],470⟩,⟨202,(9),[5,6],[174],1018⟩,⟨202,(10),[1,2,5,6,13,14],[170],471⟩,⟨202,(10),[5,6],[174],1019⟩,⟨202,(11),[1,2,5,6,13,14],[170],471⟩,⟨202,(11),[5,6],[174],1019⟩,⟨202,(12),[1,2,5,6,13,14],[170],471⟩,⟨202,(12),[5,6],[174],1019⟩,⟨202,(13),[1,2,5,6,13,14],[170],471⟩,⟨202,(13),[5,6],[174],1019⟩,⟨202,(14),[1,2,5,6,13,14],[170],470⟩,⟨202,(14),[5,6],[174],1018⟩,⟨202,(15),[1,2,5,6,13,14],[170],472⟩,⟨202,(15),[5,6],[174],1020⟩,⟨202,(16),[1,2,5,6,13,14],[170],472⟩,⟨202,(16),[5,6],[174],1020⟩,⟨202,(17),[1,2,5,6,13,14],[170],472⟩,⟨202,(17),[5,6],[174],1020⟩,⟨202,(18),[1,2,5,6,13,14],[170],472⟩,⟨202,(18),[5,6],[174],1020⟩,⟨202,(19),[1,2,5,6,13,14],[170],472⟩,⟨202,(19),[5,6],[174],1020⟩,⟨202,(20),[1,2,5,6,13,14],[170],473⟩,⟨202,(20),[5,6],[174],1021⟩,⟨202,(21),[1,2,5,6,13,14],[170],473⟩,⟨202,(21),[5,6],[174],1021⟩,⟨202,(22),[1,2,5,6,13,14],[170],473⟩,⟨202,(22),[5,6],[174],1021⟩,⟨202,(23),[1,2,5,6,13,14],[170],473⟩,⟨202,(23),[5,6],[174],1021⟩,⟨202,(24),[1,2,5,6,13,14],[170],473⟩,⟨202,(24),[5,6],[174],1021⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3200
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3201
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3202
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3203
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3204
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3205
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3206
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3207
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3208
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3209
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3210
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3211
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3212
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3213
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3214
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3215
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3216
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3217
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3218
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3219
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3220
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3221
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3222
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3223
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3224
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3225
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3226
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3227
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3228
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3229
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3230
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3231
end Section14Records_5_3200_3232

#print axioms solution
