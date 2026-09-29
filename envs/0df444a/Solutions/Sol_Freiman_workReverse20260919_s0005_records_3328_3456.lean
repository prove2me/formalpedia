-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3328_3456
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:31:09.652415+00:00
-- url     : https://prove2.me/submissions/ef0459c5-5638-41fe-ae54-4781ec59da5f

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3328_3360
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3328_3360
private theorem valid3328 : RecordDataValid section14Catalog 5 (⟨207,(23),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3329 : RecordDataValid section14Catalog 5 (⟨207,(23),[5,6],[174],1028⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1028,[3,5,6,7],1032⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3330 : RecordDataValid section14Catalog 5 (⟨207,(24),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3331 : RecordDataValid section14Catalog 5 (⟨207,(24),[5,6],[174],1028⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1028,[3,5,6,7],1032⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3332 : RecordDataValid section14Catalog 5 (⟨210,(0),[1,2,5,6,13,14],[170],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3333 : RecordDataValid section14Catalog 5 (⟨210,(0),[5,6],[174],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3334 : RecordDataValid section14Catalog 5 (⟨210,(1),[1,2,5,6,13,14],[170],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3335 : RecordDataValid section14Catalog 5 (⟨210,(1),[5,6],[174],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3336 : RecordDataValid section14Catalog 5 (⟨210,(2),[1,2,5,6,13,14],[170],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3337 : RecordDataValid section14Catalog 5 (⟨210,(2),[5,6],[174],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3338 : RecordDataValid section14Catalog 5 (⟨210,(3),[1,2,5,6,13,14],[170],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3339 : RecordDataValid section14Catalog 5 (⟨210,(3),[5,6],[174],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3340 : RecordDataValid section14Catalog 5 (⟨210,(4),[1,2,5,6,13,14],[170],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3341 : RecordDataValid section14Catalog 5 (⟨210,(4),[5,6],[174],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3342 : RecordDataValid section14Catalog 5 (⟨210,(5),[1,2,5,6,13,14],[170],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3343 : RecordDataValid section14Catalog 5 (⟨210,(5),[5,6],[174],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3344 : RecordDataValid section14Catalog 5 (⟨210,(6),[1,2,5,6,13,14],[170],726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨726,[1,2,4,5,6,8,9,10,12,13,14,16],727⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3345 : RecordDataValid section14Catalog 5 (⟨210,(6),[5,6],[174],726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨726,[1,2,4,5,6,8,9,10,12,13,14,16],727⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3346 : RecordDataValid section14Catalog 5 (⟨210,(7),[1,2,5,6,13,14],[170],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3347 : RecordDataValid section14Catalog 5 (⟨210,(7),[5,6],[174],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3348 : RecordDataValid section14Catalog 5 (⟨210,(8),[1,2,5,6,13,14],[170],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3349 : RecordDataValid section14Catalog 5 (⟨210,(8),[5,6],[174],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3350 : RecordDataValid section14Catalog 5 (⟨210,(9),[1,2,5,6,13,14],[170],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3351 : RecordDataValid section14Catalog 5 (⟨210,(9),[5,6],[174],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3352 : RecordDataValid section14Catalog 5 (⟨210,(10),[1,2,5,6,13,14],[170],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3353 : RecordDataValid section14Catalog 5 (⟨210,(10),[5,6],[174],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3354 : RecordDataValid section14Catalog 5 (⟨210,(11),[1,2,5,6,13,14],[170],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3355 : RecordDataValid section14Catalog 5 (⟨210,(11),[5,6],[174],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3356 : RecordDataValid section14Catalog 5 (⟨210,(12),[1,2,5,6,13,14],[170],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3357 : RecordDataValid section14Catalog 5 (⟨210,(12),[5,6],[174],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3358 : RecordDataValid section14Catalog 5 (⟨210,(13),[1,2,5,6,13,14],[170],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3359 : RecordDataValid section14Catalog 5 (⟨210,(13),[5,6],[174],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3328_3360 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3328).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3328).take 32 = [⟨207,(23),[1,2,5,6,13,14],[170],487⟩,⟨207,(23),[5,6],[174],1028⟩,⟨207,(24),[1,2,5,6,13,14],[170],487⟩,⟨207,(24),[5,6],[174],1028⟩,⟨210,(0),[1,2,5,6,13,14],[170],722⟩,⟨210,(0),[5,6],[174],722⟩,⟨210,(1),[1,2,5,6,13,14],[170],723⟩,⟨210,(1),[5,6],[174],723⟩,⟨210,(2),[1,2,5,6,13,14],[170],724⟩,⟨210,(2),[5,6],[174],724⟩,⟨210,(3),[1,2,5,6,13,14],[170],725⟩,⟨210,(3),[5,6],[174],725⟩,⟨210,(4),[1,2,5,6,13,14],[170],722⟩,⟨210,(4),[5,6],[174],722⟩,⟨210,(5),[1,2,5,6,13,14],[170],723⟩,⟨210,(5),[5,6],[174],723⟩,⟨210,(6),[1,2,5,6,13,14],[170],726⟩,⟨210,(6),[5,6],[174],726⟩,⟨210,(7),[1,2,5,6,13,14],[170],725⟩,⟨210,(7),[5,6],[174],725⟩,⟨210,(8),[1,2,5,6,13,14],[170],722⟩,⟨210,(8),[5,6],[174],722⟩,⟨210,(9),[1,2,5,6,13,14],[170],723⟩,⟨210,(9),[5,6],[174],723⟩,⟨210,(10),[1,2,5,6,13,14],[170],724⟩,⟨210,(10),[5,6],[174],724⟩,⟨210,(11),[1,2,5,6,13,14],[170],725⟩,⟨210,(11),[5,6],[174],725⟩,⟨210,(12),[1,2,5,6,13,14],[170],722⟩,⟨210,(12),[5,6],[174],722⟩,⟨210,(13),[1,2,5,6,13,14],[170],723⟩,⟨210,(13),[5,6],[174],723⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3328
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3329
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3330
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3331
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3332
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3333
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3334
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3335
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3336
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3337
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3338
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3339
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3340
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3341
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3342
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3343
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3344
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3345
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3346
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3347
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3348
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3349
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3350
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3351
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3352
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3353
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3354
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3355
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3356
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3357
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3358
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3359
end Section14Records_5_3328_3360

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3328_3360


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3360_3392
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3360_3392
private theorem valid3360 : RecordDataValid section14Catalog 5 (⟨210,(14),[1,2,5,6,13,14],[170],727⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨727,[1,2,4,5,6,8,9,10,12,13,14,16],728⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3361 : RecordDataValid section14Catalog 5 (⟨210,(14),[5,6],[174],727⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨727,[1,2,4,5,6,8,9,10,12,13,14,16],728⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3362 : RecordDataValid section14Catalog 5 (⟨210,(15),[1,2,5,6,13,14],[170],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3363 : RecordDataValid section14Catalog 5 (⟨210,(15),[5,6],[174],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3364 : RecordDataValid section14Catalog 5 (⟨213,(0),[1,2,5,6,13,14],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3365 : RecordDataValid section14Catalog 5 (⟨213,(0),[5,6],[174],1029⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1029,[3,5,6,7],1033⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3366 : RecordDataValid section14Catalog 5 (⟨213,(1),[1,2,5,6,13,14],[170],495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨495,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3367 : RecordDataValid section14Catalog 5 (⟨213,(1),[5,6],[174],1030⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1030,[3,5,6,7],1034⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3368 : RecordDataValid section14Catalog 5 (⟨213,(2),[1,2,5,6,13,14],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3369 : RecordDataValid section14Catalog 5 (⟨213,(2),[5,6],[174],1029⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1029,[3,5,6,7],1033⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3370 : RecordDataValid section14Catalog 5 (⟨213,(3),[1,2,5,6,13,14],[170],496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨496,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3371 : RecordDataValid section14Catalog 5 (⟨213,(3),[5,6],[174],1031⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1031,[3,5,6,7],1035⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3372 : RecordDataValid section14Catalog 5 (⟨213,(4),[1,2,5,6,13,14],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3373 : RecordDataValid section14Catalog 5 (⟨213,(4),[5,6],[174],1032⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1032,[3,5,6,7],1036⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3374 : RecordDataValid section14Catalog 5 (⟨213,(5),[1,2,5,6,13,14],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3375 : RecordDataValid section14Catalog 5 (⟨213,(5),[5,6],[174],1032⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1032,[3,5,6,7],1036⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3376 : RecordDataValid section14Catalog 5 (⟨213,(6),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3377 : RecordDataValid section14Catalog 5 (⟨213,(6),[5,6],[174],1032⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1032,[3,5,6,7],1036⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3378 : RecordDataValid section14Catalog 5 (⟨213,(7),[1,2,5,6,13,14],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3379 : RecordDataValid section14Catalog 5 (⟨213,(7),[5,6],[174],1032⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1032,[3,5,6,7],1036⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3380 : RecordDataValid section14Catalog 5 (⟨213,(8),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3381 : RecordDataValid section14Catalog 5 (⟨213,(8),[5,6],[174],1034⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1034,[3,5,6,7],1038⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3382 : RecordDataValid section14Catalog 5 (⟨213,(9),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3383 : RecordDataValid section14Catalog 5 (⟨213,(9),[5,6],[174],1034⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1034,[3,5,6,7],1038⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3384 : RecordDataValid section14Catalog 5 (⟨213,(10),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3385 : RecordDataValid section14Catalog 5 (⟨213,(10),[5,6],[174],1034⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1034,[3,5,6,7],1038⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3386 : RecordDataValid section14Catalog 5 (⟨213,(11),[1,2,5,6,13,14],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3387 : RecordDataValid section14Catalog 5 (⟨213,(11),[5,6],[174],1034⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1034,[3,5,6,7],1038⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3388 : RecordDataValid section14Catalog 5 (⟨213,(12),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3389 : RecordDataValid section14Catalog 5 (⟨213,(12),[5,6],[174],1035⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1035,[3,5,6,7],1039⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3390 : RecordDataValid section14Catalog 5 (⟨213,(13),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3391 : RecordDataValid section14Catalog 5 (⟨213,(13),[5,6],[174],1035⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1035,[3,5,6,7],1039⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3360_3392 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3360).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3360).take 32 = [⟨210,(14),[1,2,5,6,13,14],[170],727⟩,⟨210,(14),[5,6],[174],727⟩,⟨210,(15),[1,2,5,6,13,14],[170],725⟩,⟨210,(15),[5,6],[174],725⟩,⟨213,(0),[1,2,5,6,13,14],[170],494⟩,⟨213,(0),[5,6],[174],1029⟩,⟨213,(1),[1,2,5,6,13,14],[170],495⟩,⟨213,(1),[5,6],[174],1030⟩,⟨213,(2),[1,2,5,6,13,14],[170],494⟩,⟨213,(2),[5,6],[174],1029⟩,⟨213,(3),[1,2,5,6,13,14],[170],496⟩,⟨213,(3),[5,6],[174],1031⟩,⟨213,(4),[1,2,5,6,13,14],[170],497⟩,⟨213,(4),[5,6],[174],1032⟩,⟨213,(5),[1,2,5,6,13,14],[170],497⟩,⟨213,(5),[5,6],[174],1032⟩,⟨213,(6),[1,5,6,13],[170],497⟩,⟨213,(6),[5,6],[174],1032⟩,⟨213,(7),[1,2,5,6,13,14],[170],497⟩,⟨213,(7),[5,6],[174],1032⟩,⟨213,(8),[1,2,5,6,13,14],[170],498⟩,⟨213,(8),[5,6],[174],1034⟩,⟨213,(9),[1,2,5,6,13,14],[170],498⟩,⟨213,(9),[5,6],[174],1034⟩,⟨213,(10),[1,2,5,6,13,14],[170],498⟩,⟨213,(10),[5,6],[174],1034⟩,⟨213,(11),[1,2,5,6,13,14],[170],498⟩,⟨213,(11),[5,6],[174],1034⟩,⟨213,(12),[1,2,5,6,13,14],[170],499⟩,⟨213,(12),[5,6],[174],1035⟩,⟨213,(13),[1,2,5,6,13,14],[170],499⟩,⟨213,(13),[5,6],[174],1035⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3360
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3361
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3362
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3363
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3364
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3365
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3366
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3367
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3368
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3369
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3370
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3371
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3372
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3373
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3374
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3375
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3376
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3377
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3378
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3379
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3380
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3381
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3382
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3383
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3384
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3385
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3386
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3387
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3388
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3389
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3390
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3391
end Section14Records_5_3360_3392

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3360_3392


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3392_3424
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3392_3424
private theorem valid3392 : RecordDataValid section14Catalog 5 (⟨213,(14),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3393 : RecordDataValid section14Catalog 5 (⟨213,(14),[5,6],[174],1035⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1035,[3,5,6,7],1039⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3394 : RecordDataValid section14Catalog 5 (⟨213,(15),[1,2,5,6,13,14],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3395 : RecordDataValid section14Catalog 5 (⟨213,(15),[5,6],[174],1035⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1035,[3,5,6,7],1039⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3396 : RecordDataValid section14Catalog 5 (⟨215,(0),[1,2,5,6],[170],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3397 : RecordDataValid section14Catalog 5 (⟨215,(0),[5,6],[174],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3398 : RecordDataValid section14Catalog 5 (⟨215,(1),[1,2,5,6],[170],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3399 : RecordDataValid section14Catalog 5 (⟨215,(1),[5,6],[174],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3400 : RecordDataValid section14Catalog 5 (⟨215,(2),[1,2,5,6],[170],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3401 : RecordDataValid section14Catalog 5 (⟨215,(2),[5,6],[174],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3402 : RecordDataValid section14Catalog 5 (⟨215,(3),[1,2,5,6],[170],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3403 : RecordDataValid section14Catalog 5 (⟨215,(3),[5,6],[174],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3404 : RecordDataValid section14Catalog 5 (⟨215,(4),[1,2,5,6],[170],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3405 : RecordDataValid section14Catalog 5 (⟨215,(4),[5,6],[174],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3406 : RecordDataValid section14Catalog 5 (⟨215,(5),[1,2,5,6],[170],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3407 : RecordDataValid section14Catalog 5 (⟨215,(5),[5,6],[174],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3408 : RecordDataValid section14Catalog 5 (⟨215,(6),[1,2,5,6],[170],732⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨732,[1,2,4,5,6,8,9,10,12],733⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3409 : RecordDataValid section14Catalog 5 (⟨215,(6),[5,6],[174],732⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨732,[1,2,4,5,6,8,9,10,12],733⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3410 : RecordDataValid section14Catalog 5 (⟨215,(7),[1,2,5,6],[170],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3411 : RecordDataValid section14Catalog 5 (⟨215,(7),[5,6],[174],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3412 : RecordDataValid section14Catalog 5 (⟨215,(8),[1,2,5,6],[170],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3413 : RecordDataValid section14Catalog 5 (⟨215,(8),[5,6],[174],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3414 : RecordDataValid section14Catalog 5 (⟨215,(9),[1,2,5,6],[170],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3415 : RecordDataValid section14Catalog 5 (⟨215,(9),[5,6],[174],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3416 : RecordDataValid section14Catalog 5 (⟨215,(10),[1,2,5,6],[170],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3417 : RecordDataValid section14Catalog 5 (⟨215,(10),[5,6],[174],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3418 : RecordDataValid section14Catalog 5 (⟨215,(11),[1,2,5,6],[170],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3419 : RecordDataValid section14Catalog 5 (⟨215,(11),[5,6],[174],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3420 : RecordDataValid section14Catalog 5 (⟨215,(12),[1,2,5,6],[170],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3421 : RecordDataValid section14Catalog 5 (⟨215,(12),[5,6],[174],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3422 : RecordDataValid section14Catalog 5 (⟨215,(13),[1,2,5,6],[170],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3423 : RecordDataValid section14Catalog 5 (⟨215,(13),[5,6],[174],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3392_3424 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3392).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3392).take 32 = [⟨213,(14),[1,2,5,6,13,14],[170],499⟩,⟨213,(14),[5,6],[174],1035⟩,⟨213,(15),[1,2,5,6,13,14],[170],499⟩,⟨213,(15),[5,6],[174],1035⟩,⟨215,(0),[1,2,5,6],[170],728⟩,⟨215,(0),[5,6],[174],728⟩,⟨215,(1),[1,2,5,6],[170],729⟩,⟨215,(1),[5,6],[174],729⟩,⟨215,(2),[1,2,5,6],[170],730⟩,⟨215,(2),[5,6],[174],730⟩,⟨215,(3),[1,2,5,6],[170],731⟩,⟨215,(3),[5,6],[174],731⟩,⟨215,(4),[1,2,5,6],[170],728⟩,⟨215,(4),[5,6],[174],728⟩,⟨215,(5),[1,2,5,6],[170],729⟩,⟨215,(5),[5,6],[174],729⟩,⟨215,(6),[1,2,5,6],[170],732⟩,⟨215,(6),[5,6],[174],732⟩,⟨215,(7),[1,2,5,6],[170],731⟩,⟨215,(7),[5,6],[174],731⟩,⟨215,(8),[1,2,5,6],[170],728⟩,⟨215,(8),[5,6],[174],728⟩,⟨215,(9),[1,2,5,6],[170],729⟩,⟨215,(9),[5,6],[174],729⟩,⟨215,(10),[1,2,5,6],[170],730⟩,⟨215,(10),[5,6],[174],730⟩,⟨215,(11),[1,2,5,6],[170],731⟩,⟨215,(11),[5,6],[174],731⟩,⟨215,(12),[1,2,5,6],[170],728⟩,⟨215,(12),[5,6],[174],728⟩,⟨215,(13),[1,2,5,6],[170],729⟩,⟨215,(13),[5,6],[174],729⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3392
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3393
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3394
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3395
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3396
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3397
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3398
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3399
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3400
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3401
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3402
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3403
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3404
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3405
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3406
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3407
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3408
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3409
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3410
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3411
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3412
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3413
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3414
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3415
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3416
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3417
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3418
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3419
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3420
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3421
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3422
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3423
end Section14Records_5_3392_3424

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3392_3424


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3424_3456
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3424_3456
private theorem valid3424 : RecordDataValid section14Catalog 5 (⟨215,(14),[1,2,5,6],[170],733⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨733,[1,2,4,5,6,8,9,10,12],734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3425 : RecordDataValid section14Catalog 5 (⟨215,(14),[5,6],[174],733⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨733,[1,2,4,5,6,8,9,10,12],734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3426 : RecordDataValid section14Catalog 5 (⟨215,(15),[1,2,5,6],[170],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3427 : RecordDataValid section14Catalog 5 (⟨215,(15),[5,6],[174],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3428 : RecordDataValid section14Catalog 5 (⟨218,(0),[1,2,5,6],[170],506⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨506,[1,2,3,4,5,6,7,8,9,10,11,12],507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3429 : RecordDataValid section14Catalog 5 (⟨218,(0),[5,6],[174],307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨307,[1,2,3,5,6,7],308⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3430 : RecordDataValid section14Catalog 5 (⟨218,(1),[1,2,5,6],[170],507⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨507,[1,2,3,4,5,6,7,8,9,10,11,12],508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3431 : RecordDataValid section14Catalog 5 (⟨218,(1),[5,6],[174],308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨308,[1,2,3,5,6,7],309⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3432 : RecordDataValid section14Catalog 5 (⟨218,(2),[1,2,5,6],[170],508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨508,[1,2,3,4,5,6,7,8,9,10,11,12],509⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3433 : RecordDataValid section14Catalog 5 (⟨218,(2),[5,6],[174],309⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨309,[1,2,3,5,6,7],310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3434 : RecordDataValid section14Catalog 5 (⟨218,(3),[1,2,5,6],[170],509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨509,[1,2,3,4,5,6,7,8,9,10,11,12],510⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3435 : RecordDataValid section14Catalog 5 (⟨218,(3),[5,6],[174],310⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨310,[1,2,3,5,6,7],311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3436 : RecordDataValid section14Catalog 5 (⟨220,(0),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3437 : RecordDataValid section14Catalog 5 (⟨220,(0),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3438 : RecordDataValid section14Catalog 5 (⟨220,(1),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3439 : RecordDataValid section14Catalog 5 (⟨220,(1),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3440 : RecordDataValid section14Catalog 5 (⟨220,(2),[1,2,5,6,13,14],[170],734⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨734,[1,2,5,6,9,10,13,14],735⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3441 : RecordDataValid section14Catalog 5 (⟨220,(2),[5,6],[174],734⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨734,[1,2,5,6,9,10,13,14],735⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3442 : RecordDataValid section14Catalog 5 (⟨220,(3),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3443 : RecordDataValid section14Catalog 5 (⟨220,(3),[5,6],[174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3444 : RecordDataValid section14Catalog 5 (⟨220,(4),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3445 : RecordDataValid section14Catalog 5 (⟨220,(4),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3446 : RecordDataValid section14Catalog 5 (⟨220,(5),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3447 : RecordDataValid section14Catalog 5 (⟨220,(5),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3448 : RecordDataValid section14Catalog 5 (⟨220,(6),[1,2,5,6,13,14],[170],511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨511,[1,2,5,6,9,10,13,14],512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3449 : RecordDataValid section14Catalog 5 (⟨220,(6),[5,6],[174],511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨511,[1,2,5,6,9,10,13,14],512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3450 : RecordDataValid section14Catalog 5 (⟨220,(7),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3451 : RecordDataValid section14Catalog 5 (⟨220,(7),[5,6],[174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3452 : RecordDataValid section14Catalog 5 (⟨220,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3453 : RecordDataValid section14Catalog 5 (⟨220,(8),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3454 : RecordDataValid section14Catalog 5 (⟨220,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3455 : RecordDataValid section14Catalog 5 (⟨220,(9),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3424_3456 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3424).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3424).take 32 = [⟨215,(14),[1,2,5,6],[170],733⟩,⟨215,(14),[5,6],[174],733⟩,⟨215,(15),[1,2,5,6],[170],731⟩,⟨215,(15),[5,6],[174],731⟩,⟨218,(0),[1,2,5,6],[170],506⟩,⟨218,(0),[5,6],[174],307⟩,⟨218,(1),[1,2,5,6],[170],507⟩,⟨218,(1),[5,6],[174],308⟩,⟨218,(2),[1,2,5,6],[170],508⟩,⟨218,(2),[5,6],[174],309⟩,⟨218,(3),[1,2,5,6],[170],509⟩,⟨218,(3),[5,6],[174],310⟩,⟨220,(0),[1,2,5,6,13,14],[170],3⟩,⟨220,(0),[5,6],[174],3⟩,⟨220,(1),[1,2,5,6,13,14],[170],3⟩,⟨220,(1),[5,6],[174],3⟩,⟨220,(2),[1,2,5,6,13,14],[170],734⟩,⟨220,(2),[5,6],[174],734⟩,⟨220,(3),[1,2,5,6,13,14],[170],29⟩,⟨220,(3),[5,6],[174],29⟩,⟨220,(4),[1,2,5,6,13,14],[170],3⟩,⟨220,(4),[5,6],[174],3⟩,⟨220,(5),[1,2,5,6,13,14],[170],3⟩,⟨220,(5),[5,6],[174],3⟩,⟨220,(6),[1,2,5,6,13,14],[170],511⟩,⟨220,(6),[5,6],[174],511⟩,⟨220,(7),[1,2,5,6,13,14],[170],29⟩,⟨220,(7),[5,6],[174],29⟩,⟨220,(8),[1,2,5,6,13,14],[170],3⟩,⟨220,(8),[5,6],[174],3⟩,⟨220,(9),[1,2,5,6,13,14],[170],3⟩,⟨220,(9),[5,6],[174],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3424
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3425
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3426
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3427
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3428
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3429
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3430
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3431
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3432
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3433
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3434
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3435
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3436
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3437
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3438
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3439
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3440
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3441
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3442
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3443
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3444
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3445
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3446
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3447
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3448
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3449
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3450
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3451
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3452
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3453
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3454
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3455
end Section14Records_5_3424_3456

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3424_3456

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3328).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 3328 3392 3456 (by decide) (by decide) (all_of_interval_split P xs 3328 3360 3392 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_3328_3360 hnum) (Freiman.workReverse20260919_s0005_records_3360_3392 hnum)) (all_of_interval_split P xs 3392 3424 3456 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_3392_3424 hnum) (Freiman.workReverse20260919_s0005_records_3424_3456 hnum)))

#print axioms solution
