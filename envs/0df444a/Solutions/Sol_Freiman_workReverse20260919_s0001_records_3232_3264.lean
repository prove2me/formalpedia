-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3232_3264
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:04:14.711166+00:00
-- url     : https://prove2.me/submissions/c1e4485e-ad8f-4dc5-8e1e-15b908a3514d

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
namespace Section14Records_1_3232_3264
private theorem valid3232 : RecordDataValid section14Catalog 1 (⟨190,(20),[1,2,5,6,13,14],[170],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3233 : RecordDataValid section14Catalog 1 (⟨190,(21),[1,2,5,6,13,14],[170],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3234 : RecordDataValid section14Catalog 1 (⟨190,(22),[1,2,5,6,13,14],[170],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3235 : RecordDataValid section14Catalog 1 (⟨190,(23),[1,2,5,6,13,14],[170],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3236 : RecordDataValid section14Catalog 1 (⟨190,(24),[1,2,5,6,13,14],[170],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3237 : RecordDataValid section14Catalog 1 (⟨192,(0),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3238 : RecordDataValid section14Catalog 1 (⟨192,(1),[1,2,5,6,13,14],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3239 : RecordDataValid section14Catalog 1 (⟨192,(2),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3240 : RecordDataValid section14Catalog 1 (⟨192,(3),[1,2,5,6,13,14],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3241 : RecordDataValid section14Catalog 1 (⟨192,(4),[1,2,5,6,13,14],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3242 : RecordDataValid section14Catalog 1 (⟨192,(5),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3243 : RecordDataValid section14Catalog 1 (⟨192,(6),[1,2,5,6,13,14],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3244 : RecordDataValid section14Catalog 1 (⟨192,(7),[1,2,5,6,13,14],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3245 : RecordDataValid section14Catalog 1 (⟨192,(8),[1,2,5,6,13,14],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3246 : RecordDataValid section14Catalog 1 (⟨192,(9),[1,2,5,6,13,14],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3247 : RecordDataValid section14Catalog 1 (⟨192,(10),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3248 : RecordDataValid section14Catalog 1 (⟨192,(11),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3249 : RecordDataValid section14Catalog 1 (⟨192,(12),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3250 : RecordDataValid section14Catalog 1 (⟨192,(13),[1,2,5,6,13,14],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3251 : RecordDataValid section14Catalog 1 (⟨192,(14),[1,2,5,6,13,14],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3252 : RecordDataValid section14Catalog 1 (⟨192,(15),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3253 : RecordDataValid section14Catalog 1 (⟨192,(16),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3254 : RecordDataValid section14Catalog 1 (⟨192,(17),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3255 : RecordDataValid section14Catalog 1 (⟨192,(18),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3256 : RecordDataValid section14Catalog 1 (⟨192,(19),[1,2,5,6,13,14],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3257 : RecordDataValid section14Catalog 1 (⟨192,(20),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3258 : RecordDataValid section14Catalog 1 (⟨192,(21),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3259 : RecordDataValid section14Catalog 1 (⟨192,(22),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3260 : RecordDataValid section14Catalog 1 (⟨192,(23),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3261 : RecordDataValid section14Catalog 1 (⟨192,(24),[1,2,5,6,13,14],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3262 : RecordDataValid section14Catalog 1 (⟨195,(0),[1,2,5,6,13,14],[170],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3263 : RecordDataValid section14Catalog 1 (⟨195,(1),[1,2,5,6,13,14],[170],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3232).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3232).take 32 = [⟨190,(20),[1,2,5,6,13,14],[170],692⟩,⟨190,(21),[1,2,5,6,13,14],[170],693⟩,⟨190,(22),[1,2,5,6,13,14],[170],694⟩,⟨190,(23),[1,2,5,6,13,14],[170],693⟩,⟨190,(24),[1,2,5,6,13,14],[170],695⟩,⟨192,(0),[1,2,5,6,13,14],[170],441⟩,⟨192,(1),[1,2,5,6,13,14],[170],442⟩,⟨192,(2),[1,2,5,6,13,14],[170],441⟩,⟨192,(3),[1,2,5,6,13,14],[170],443⟩,⟨192,(4),[1,2,5,6,13,14],[170],444⟩,⟨192,(5),[1,2,5,6,13,14],[170],441⟩,⟨192,(6),[1,2,5,6,13,14],[170],442⟩,⟨192,(7),[1,2,5,6,13,14],[170],441⟩,⟨192,(8),[1,2,5,6,13,14],[170],443⟩,⟨192,(9),[1,2,5,6,13,14],[170],444⟩,⟨192,(10),[1,2,5,6,13,14],[170],445⟩,⟨192,(11),[1,2,5,6,13,14],[170],445⟩,⟨192,(12),[1,2,5,6,13,14],[170],445⟩,⟨192,(13),[1,2,5,6,13,14],[170],445⟩,⟨192,(14),[1,2,5,6,13,14],[170],444⟩,⟨192,(15),[1,2,5,6,13,14],[170],446⟩,⟨192,(16),[1,2,5,6,13,14],[170],446⟩,⟨192,(17),[1,2,5,6,13,14],[170],446⟩,⟨192,(18),[1,2,5,6,13,14],[170],446⟩,⟨192,(19),[1,2,5,6,13,14],[170],446⟩,⟨192,(20),[1,2,5,6,13,14],[170],447⟩,⟨192,(21),[1,2,5,6,13,14],[170],447⟩,⟨192,(22),[1,2,5,6,13,14],[170],447⟩,⟨192,(23),[1,2,5,6,13,14],[170],447⟩,⟨192,(24),[1,2,5,6,13,14],[170],447⟩,⟨195,(0),[1,2,5,6,13,14],[170],697⟩,⟨195,(1),[1,2,5,6,13,14],[170],697⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3232
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3233
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3234
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3235
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3236
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3237
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3238
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3239
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3240
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3241
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3242
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3243
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3244
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3245
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3246
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3247
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3248
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3249
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3250
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3251
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3252
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3253
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3254
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3255
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3256
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3257
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3258
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3259
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3260
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3261
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3262
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3263
end Section14Records_1_3232_3264

#print axioms solution
