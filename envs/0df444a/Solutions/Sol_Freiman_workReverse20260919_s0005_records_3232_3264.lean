-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3232_3264
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:56:03.958117+00:00
-- url     : https://prove2.me/submissions/75bfd642-54c6-4677-9fe7-e1e76c218d4f

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
namespace Section14Records_5_3232_3264
private theorem valid3232 : RecordDataValid section14Catalog 5 (⟨205,(0),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3233 : RecordDataValid section14Catalog 5 (⟨205,(0),[5,6],[174],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3234 : RecordDataValid section14Catalog 5 (⟨205,(1),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3235 : RecordDataValid section14Catalog 5 (⟨205,(1),[5,6],[174],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3236 : RecordDataValid section14Catalog 5 (⟨205,(2),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3237 : RecordDataValid section14Catalog 5 (⟨205,(2),[5,6],[174],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3238 : RecordDataValid section14Catalog 5 (⟨205,(3),[1,2,5,6,13,14],[170],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3239 : RecordDataValid section14Catalog 5 (⟨205,(3),[5,6],[174],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3240 : RecordDataValid section14Catalog 5 (⟨205,(4),[1,2,5,6,13,14],[170],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3241 : RecordDataValid section14Catalog 5 (⟨205,(4),[5,6],[174],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3242 : RecordDataValid section14Catalog 5 (⟨205,(5),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3243 : RecordDataValid section14Catalog 5 (⟨205,(5),[5,6],[174],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3244 : RecordDataValid section14Catalog 5 (⟨205,(6),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3245 : RecordDataValid section14Catalog 5 (⟨205,(6),[5,6],[174],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3246 : RecordDataValid section14Catalog 5 (⟨205,(7),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3247 : RecordDataValid section14Catalog 5 (⟨205,(7),[5,6],[174],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3248 : RecordDataValid section14Catalog 5 (⟨205,(8),[1,2,5,6,13,14],[170],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3249 : RecordDataValid section14Catalog 5 (⟨205,(8),[5,6],[174],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3250 : RecordDataValid section14Catalog 5 (⟨205,(9),[1,2,5,6,13,14],[170],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3251 : RecordDataValid section14Catalog 5 (⟨205,(9),[5,6],[174],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3252 : RecordDataValid section14Catalog 5 (⟨205,(10),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3253 : RecordDataValid section14Catalog 5 (⟨205,(10),[5,6],[174],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3254 : RecordDataValid section14Catalog 5 (⟨205,(11),[1,2,5,6,13,14],[170],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3255 : RecordDataValid section14Catalog 5 (⟨205,(11),[5,6],[174],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3256 : RecordDataValid section14Catalog 5 (⟨205,(12),[1,2,5,6,13,14],[170],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3257 : RecordDataValid section14Catalog 5 (⟨205,(12),[5,6],[174],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3258 : RecordDataValid section14Catalog 5 (⟨205,(13),[1,2,5,6,13,14],[170],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3259 : RecordDataValid section14Catalog 5 (⟨205,(13),[5,6],[174],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3260 : RecordDataValid section14Catalog 5 (⟨205,(14),[1,2,5,6,13,14],[170],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3261 : RecordDataValid section14Catalog 5 (⟨205,(14),[5,6],[174],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3262 : RecordDataValid section14Catalog 5 (⟨205,(15),[1,2,5,6,13,14],[170],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3263 : RecordDataValid section14Catalog 5 (⟨205,(15),[5,6],[174],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3232).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3232).take 32 = [⟨205,(0),[1,2,5,6,13,14],[170],711⟩,⟨205,(0),[5,6],[174],711⟩,⟨205,(1),[1,2,5,6,13,14],[170],711⟩,⟨205,(1),[5,6],[174],711⟩,⟨205,(2),[1,2,5,6,13,14],[170],711⟩,⟨205,(2),[5,6],[174],711⟩,⟨205,(3),[1,2,5,6,13,14],[170],712⟩,⟨205,(3),[5,6],[174],712⟩,⟨205,(4),[1,2,5,6,13,14],[170],711⟩,⟨205,(4),[5,6],[174],711⟩,⟨205,(5),[1,2,5,6,13,14],[170],713⟩,⟨205,(5),[5,6],[174],713⟩,⟨205,(6),[1,2,5,6,13,14],[170],713⟩,⟨205,(6),[5,6],[174],713⟩,⟨205,(7),[1,2,5,6,13,14],[170],713⟩,⟨205,(7),[5,6],[174],713⟩,⟨205,(8),[1,2,5,6,13,14],[170],714⟩,⟨205,(8),[5,6],[174],714⟩,⟨205,(9),[1,2,5,6,13,14],[170],713⟩,⟨205,(9),[5,6],[174],713⟩,⟨205,(10),[1,2,5,6,13,14],[170],715⟩,⟨205,(10),[5,6],[174],715⟩,⟨205,(11),[1,2,5,6,13,14],[170],716⟩,⟨205,(11),[5,6],[174],716⟩,⟨205,(12),[1,2,5,6,13,14],[170],717⟩,⟨205,(12),[5,6],[174],717⟩,⟨205,(13),[1,2,5,6,13,14],[170],718⟩,⟨205,(13),[5,6],[174],718⟩,⟨205,(14),[1,2,5,6,13,14],[170],719⟩,⟨205,(14),[5,6],[174],719⟩,⟨205,(15),[1,2,5,6,13,14],[170],715⟩,⟨205,(15),[5,6],[174],715⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3232
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3233
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3234
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3235
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3236
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3237
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3238
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3239
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3240
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3241
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3242
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3243
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3244
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3245
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3246
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3247
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3248
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3249
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3250
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3251
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3252
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3253
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3254
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3255
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3256
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3257
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3258
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3259
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3260
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3261
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3262
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3263
end Section14Records_5_3232_3264

#print axioms solution
