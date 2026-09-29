-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3264_3328
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:29:03.889478+00:00
-- url     : https://prove2.me/submissions/29efd2cb-8f9b-4453-bd4f-7d6dfba4c16a

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3264_3296
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3264_3296
private theorem valid3264 : RecordDataValid section14Catalog 6 (⟨222,(14),[5,6],[174],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3265 : RecordDataValid section14Catalog 6 (⟨222,(15),[1,2,5,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3266 : RecordDataValid section14Catalog 6 (⟨222,(15),[5,6],[174],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3267 : RecordDataValid section14Catalog 6 (⟨222,(16),[1,2,5,6,13,14],[170],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3268 : RecordDataValid section14Catalog 6 (⟨222,(16),[5,6],[174],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3269 : RecordDataValid section14Catalog 6 (⟨222,(17),[1,2,5,6,13,14],[170],745⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨745,[1,2,3,4,5,6,7,10,11,13,14,15,16],746⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3270 : RecordDataValid section14Catalog 6 (⟨222,(17),[5,6],[174],745⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨745,[1,2,3,4,5,6,7,10,11,13,14,15,16],746⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3271 : RecordDataValid section14Catalog 6 (⟨222,(18),[1,2,5,6,13,14],[170],746⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨746,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],747⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3272 : RecordDataValid section14Catalog 6 (⟨222,(18),[5,6],[174],746⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨746,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],747⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3273 : RecordDataValid section14Catalog 6 (⟨222,(19),[1,2,5,6,13,14],[170],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3274 : RecordDataValid section14Catalog 6 (⟨222,(19),[5,6],[174],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3275 : RecordDataValid section14Catalog 6 (⟨222,(20),[1,2,5,6,13,14],[170],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3276 : RecordDataValid section14Catalog 6 (⟨222,(20),[5,6],[174],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3277 : RecordDataValid section14Catalog 6 (⟨222,(21),[1,2,5,6,13,14],[170],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3278 : RecordDataValid section14Catalog 6 (⟨222,(21),[5,6],[174],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3279 : RecordDataValid section14Catalog 6 (⟨222,(22),[1,2,5,6,13,14],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3280 : RecordDataValid section14Catalog 6 (⟨222,(22),[5,6],[174],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3281 : RecordDataValid section14Catalog 6 (⟨222,(23),[1,2,5,6,13,14],[170],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3282 : RecordDataValid section14Catalog 6 (⟨222,(23),[5,6],[174],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3283 : RecordDataValid section14Catalog 6 (⟨222,(24),[1,2,5,6,13,14],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3284 : RecordDataValid section14Catalog 6 (⟨222,(24),[5,6],[174],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3285 : RecordDataValid section14Catalog 6 (⟨224,(0),[1,2,5,6,13,14],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3286 : RecordDataValid section14Catalog 6 (⟨224,(0),[5,6],[174],1044⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1044,[3,5,6,7],1048⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3287 : RecordDataValid section14Catalog 6 (⟨224,(1),[1,2,5,6,13,14],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3288 : RecordDataValid section14Catalog 6 (⟨224,(1),[5,6],[174],1044⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1044,[3,5,6,7],1048⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3289 : RecordDataValid section14Catalog 6 (⟨224,(2),[1,2,5,6,13,14],[170],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3290 : RecordDataValid section14Catalog 6 (⟨224,(2),[5,6],[174],1045⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1045,[3,5,6,7],1049⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3291 : RecordDataValid section14Catalog 6 (⟨224,(3),[1,2,5,6,13,14],[170],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3292 : RecordDataValid section14Catalog 6 (⟨224,(3),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3293 : RecordDataValid section14Catalog 6 (⟨224,(4),[1,2,5,6,13,14],[170],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3294 : RecordDataValid section14Catalog 6 (⟨224,(4),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3295 : RecordDataValid section14Catalog 6 (⟨224,(5),[1,2,5,6,13,14],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3264_3296 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3264).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3264).take 32 = [⟨222,(14),[5,6],[174],531⟩,⟨222,(15),[1,2,5,6,13,14],[170],735⟩,⟨222,(15),[5,6],[174],735⟩,⟨222,(16),[1,2,5,6,13,14],[170],738⟩,⟨222,(16),[5,6],[174],738⟩,⟨222,(17),[1,2,5,6,13,14],[170],745⟩,⟨222,(17),[5,6],[174],745⟩,⟨222,(18),[1,2,5,6,13,14],[170],746⟩,⟨222,(18),[5,6],[174],746⟩,⟨222,(19),[1,2,5,6,13,14],[170],534⟩,⟨222,(19),[5,6],[174],534⟩,⟨222,(20),[1,2,5,6,13,14],[170],535⟩,⟨222,(20),[5,6],[174],535⟩,⟨222,(21),[1,2,5,6,13,14],[170],536⟩,⟨222,(21),[5,6],[174],536⟩,⟨222,(22),[1,2,5,6,13,14],[170],537⟩,⟨222,(22),[5,6],[174],537⟩,⟨222,(23),[1,2,5,6,13,14],[170],538⟩,⟨222,(23),[5,6],[174],538⟩,⟨222,(24),[1,2,5,6,13,14],[170],537⟩,⟨222,(24),[5,6],[174],537⟩,⟨224,(0),[1,2,5,6,13,14],[170],539⟩,⟨224,(0),[5,6],[174],1044⟩,⟨224,(1),[1,2,5,6,13,14],[170],539⟩,⟨224,(1),[5,6],[174],1044⟩,⟨224,(2),[1,2,5,6,13,14],[170],540⟩,⟨224,(2),[5,6],[174],1045⟩,⟨224,(3),[1,2,5,6,13,14],[170],541⟩,⟨224,(3),[5,6],[174],1038⟩,⟨224,(4),[1,2,5,6,13,14],[170],542⟩,⟨224,(4),[5,6],[174],1039⟩,⟨224,(5),[1,2,5,6,13,14],[170],543⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3264
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3265
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3266
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3267
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3268
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3269
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3270
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3271
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3272
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3273
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3274
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3275
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3276
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3277
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3278
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3279
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3280
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3281
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3282
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3283
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3284
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3285
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3286
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3287
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3288
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3289
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3290
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3291
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3292
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3293
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3294
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3295
end Section14Records_6_3264_3296

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3264_3296


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3296_3328
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3296_3328
private theorem valid3296 : RecordDataValid section14Catalog 6 (⟨224,(5),[5,6],[174],1046⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1046,[3,5,6,7],1050⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3297 : RecordDataValid section14Catalog 6 (⟨224,(6),[1,2,5,6,13,14],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3298 : RecordDataValid section14Catalog 6 (⟨224,(6),[5,6],[174],1046⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1046,[3,5,6,7],1050⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3299 : RecordDataValid section14Catalog 6 (⟨224,(7),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3300 : RecordDataValid section14Catalog 6 (⟨224,(7),[5,6],[174],1045⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1045,[3,5,6,7],1049⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3301 : RecordDataValid section14Catalog 6 (⟨224,(8),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3302 : RecordDataValid section14Catalog 6 (⟨224,(8),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3303 : RecordDataValid section14Catalog 6 (⟨224,(9),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3304 : RecordDataValid section14Catalog 6 (⟨224,(9),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3305 : RecordDataValid section14Catalog 6 (⟨224,(10),[1,2,5,6,13,14],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3306 : RecordDataValid section14Catalog 6 (⟨224,(10),[5,6],[174],1044⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1044,[3,5,6,7],1048⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3307 : RecordDataValid section14Catalog 6 (⟨224,(11),[1,2,5,6,13,14],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3308 : RecordDataValid section14Catalog 6 (⟨224,(11),[5,6],[174],1044⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1044,[3,5,6,7],1048⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3309 : RecordDataValid section14Catalog 6 (⟨224,(12),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3310 : RecordDataValid section14Catalog 6 (⟨224,(12),[5,6],[174],1045⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1045,[3,5,6,7],1049⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3311 : RecordDataValid section14Catalog 6 (⟨224,(13),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3312 : RecordDataValid section14Catalog 6 (⟨224,(13),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3313 : RecordDataValid section14Catalog 6 (⟨224,(14),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3314 : RecordDataValid section14Catalog 6 (⟨224,(14),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3315 : RecordDataValid section14Catalog 6 (⟨224,(15),[1,2,5,6,13,14],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3316 : RecordDataValid section14Catalog 6 (⟨224,(15),[5,6],[174],1047⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1047,[3,5,6,7],1051⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3317 : RecordDataValid section14Catalog 6 (⟨224,(16),[1,2,5,6,13,14],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3318 : RecordDataValid section14Catalog 6 (⟨224,(16),[5,6],[174],1047⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1047,[3,5,6,7],1051⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3319 : RecordDataValid section14Catalog 6 (⟨224,(17),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3320 : RecordDataValid section14Catalog 6 (⟨224,(17),[5,6],[174],1045⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1045,[3,5,6,7],1049⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3321 : RecordDataValid section14Catalog 6 (⟨224,(18),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3322 : RecordDataValid section14Catalog 6 (⟨224,(18),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3323 : RecordDataValid section14Catalog 6 (⟨224,(19),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3324 : RecordDataValid section14Catalog 6 (⟨224,(19),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3325 : RecordDataValid section14Catalog 6 (⟨224,(20),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3326 : RecordDataValid section14Catalog 6 (⟨224,(20),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3327 : RecordDataValid section14Catalog 6 (⟨224,(21),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3296_3328 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3296).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3296).take 32 = [⟨224,(5),[5,6],[174],1046⟩,⟨224,(6),[1,2,5,6,13,14],[170],543⟩,⟨224,(6),[5,6],[174],1046⟩,⟨224,(7),[1,2,5,6,13,14],[170],544⟩,⟨224,(7),[5,6],[174],1045⟩,⟨224,(8),[1,2,5,6,13,14],[170],517⟩,⟨224,(8),[5,6],[174],1038⟩,⟨224,(9),[1,2,5,6,13,14],[170],518⟩,⟨224,(9),[5,6],[174],1039⟩,⟨224,(10),[1,2,5,6,13,14],[170],545⟩,⟨224,(10),[5,6],[174],1044⟩,⟨224,(11),[1,2,5,6,13,14],[170],545⟩,⟨224,(11),[5,6],[174],1044⟩,⟨224,(12),[1,2,5,6,13,14],[170],544⟩,⟨224,(12),[5,6],[174],1045⟩,⟨224,(13),[1,2,5,6,13,14],[170],517⟩,⟨224,(13),[5,6],[174],1038⟩,⟨224,(14),[1,2,5,6,13,14],[170],518⟩,⟨224,(14),[5,6],[174],1039⟩,⟨224,(15),[1,2,5,6,13,14],[170],546⟩,⟨224,(15),[5,6],[174],1047⟩,⟨224,(16),[1,2,5,6,13,14],[170],546⟩,⟨224,(16),[5,6],[174],1047⟩,⟨224,(17),[1,2,5,6,13,14],[170],544⟩,⟨224,(17),[5,6],[174],1045⟩,⟨224,(18),[1,2,5,6,13,14],[170],517⟩,⟨224,(18),[5,6],[174],1038⟩,⟨224,(19),[1,2,5,6,13,14],[170],518⟩,⟨224,(19),[5,6],[174],1039⟩,⟨224,(20),[1,2,5,6,13,14],[170],547⟩,⟨224,(20),[5,6],[174],1048⟩,⟨224,(21),[1,2,5,6,13,14],[170],547⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3296
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3297
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3298
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3299
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3300
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3301
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3302
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3303
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3304
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3305
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3306
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3307
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3308
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3309
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3310
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3311
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3312
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3313
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3314
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3315
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3316
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3317
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3318
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3319
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3320
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3321
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3322
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3323
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3324
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3325
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3326
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3327
end Section14Records_6_3296_3328

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3296_3328

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3264).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 3264 3296 3328 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3264_3296 hnum) (Freiman.workReverse20260919_s0006_records_3296_3328 hnum))

#print axioms solution
