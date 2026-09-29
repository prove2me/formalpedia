-- Prove2me | solution 1 for Freiman.section14_s0016_records_0384_0416
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T00:46:07.170792+00:00
-- url     : https://prove2.me/submissions/bdea3138-0bc9-4112-96bc-f205fbf40843

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
namespace Section14Records_16_384_416
private theorem valid384 : RecordDataValid section14Catalog 16 (⟨86,(24),[4,8,16],[10],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid385 : RecordDataValid section14Catalog 16 (⟨89,(0),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid386 : RecordDataValid section14Catalog 16 (⟨89,(1),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid387 : RecordDataValid section14Catalog 16 (⟨89,(2),[4,8,12,16],[10],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid388 : RecordDataValid section14Catalog 16 (⟨89,(3),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid389 : RecordDataValid section14Catalog 16 (⟨89,(4),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid390 : RecordDataValid section14Catalog 16 (⟨89,(5),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid391 : RecordDataValid section14Catalog 16 (⟨89,(6),[4,8,12,16],[10],404⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨404,[1,4,5,6,8,9,10,12,13,16],405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid392 : RecordDataValid section14Catalog 16 (⟨89,(7),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid393 : RecordDataValid section14Catalog 16 (⟨89,(8),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid394 : RecordDataValid section14Catalog 16 (⟨89,(9),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid395 : RecordDataValid section14Catalog 16 (⟨89,(10),[4,8,12,16],[10],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid396 : RecordDataValid section14Catalog 16 (⟨89,(11),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid397 : RecordDataValid section14Catalog 16 (⟨89,(12),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid398 : RecordDataValid section14Catalog 16 (⟨89,(13),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid399 : RecordDataValid section14Catalog 16 (⟨89,(14),[4,8,12,16],[10],405⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨405,[1,4,5,6,8,9,10,12,13,16],406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid400 : RecordDataValid section14Catalog 16 (⟨89,(15),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid401 : RecordDataValid section14Catalog 16 (⟨92,(0),[4,8,12,16],[10],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid402 : RecordDataValid section14Catalog 16 (⟨92,(1),[4,8,12,16],[10],407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid403 : RecordDataValid section14Catalog 16 (⟨92,(2),[4,8,12,16],[10],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid404 : RecordDataValid section14Catalog 16 (⟨92,(3),[4,8,12,16],[10],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid405 : RecordDataValid section14Catalog 16 (⟨92,(4),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid406 : RecordDataValid section14Catalog 16 (⟨92,(5),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid407 : RecordDataValid section14Catalog 16 (⟨92,(6),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid408 : RecordDataValid section14Catalog 16 (⟨92,(7),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid409 : RecordDataValid section14Catalog 16 (⟨92,(8),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid410 : RecordDataValid section14Catalog 16 (⟨92,(9),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid411 : RecordDataValid section14Catalog 16 (⟨92,(10),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid412 : RecordDataValid section14Catalog 16 (⟨92,(11),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid413 : RecordDataValid section14Catalog 16 (⟨92,(12),[4,8,12,16],[10],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid414 : RecordDataValid section14Catalog 16 (⟨92,(13),[4,8,12,16],[10],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid415 : RecordDataValid section14Catalog 16 (⟨92,(14),[4,8,12,16],[10],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 384).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 384).take 32 = [⟨86,(24),[4,8,16],[10],399⟩,⟨89,(0),[4,8,12,16],[10],400⟩,⟨89,(1),[4,8,12,16],[10],401⟩,⟨89,(2),[4,8,12,16],[10],402⟩,⟨89,(3),[4,8,12,16],[10],403⟩,⟨89,(4),[4,8,12,16],[10],400⟩,⟨89,(5),[4,8,12,16],[10],401⟩,⟨89,(6),[4,8,12,16],[10],404⟩,⟨89,(7),[4,8,12,16],[10],403⟩,⟨89,(8),[4,8,12,16],[10],400⟩,⟨89,(9),[4,8,12,16],[10],401⟩,⟨89,(10),[4,8,12,16],[10],402⟩,⟨89,(11),[4,8,12,16],[10],403⟩,⟨89,(12),[4,8,12,16],[10],400⟩,⟨89,(13),[4,8,12,16],[10],401⟩,⟨89,(14),[4,8,12,16],[10],405⟩,⟨89,(15),[4,8,12,16],[10],403⟩,⟨92,(0),[4,8,12,16],[10],406⟩,⟨92,(1),[4,8,12,16],[10],407⟩,⟨92,(2),[4,8,12,16],[10],406⟩,⟨92,(3),[4,8,12,16],[10],408⟩,⟨92,(4),[4,8,12,16],[10],409⟩,⟨92,(5),[4,8,12,16],[10],409⟩,⟨92,(6),[4,8,12,16],[10],409⟩,⟨92,(7),[4,8,12,16],[10],409⟩,⟨92,(8),[4,8,12,16],[10],410⟩,⟨92,(9),[4,8,12,16],[10],410⟩,⟨92,(10),[4,8,12,16],[10],410⟩,⟨92,(11),[4,8,12,16],[10],410⟩,⟨92,(12),[4,8,12,16],[10],411⟩,⟨92,(13),[4,8,12,16],[10],411⟩,⟨92,(14),[4,8,12,16],[10],411⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid384
  · exact recordValid_of_data section14Catalog 16 _ hnum valid385
  · exact recordValid_of_data section14Catalog 16 _ hnum valid386
  · exact recordValid_of_data section14Catalog 16 _ hnum valid387
  · exact recordValid_of_data section14Catalog 16 _ hnum valid388
  · exact recordValid_of_data section14Catalog 16 _ hnum valid389
  · exact recordValid_of_data section14Catalog 16 _ hnum valid390
  · exact recordValid_of_data section14Catalog 16 _ hnum valid391
  · exact recordValid_of_data section14Catalog 16 _ hnum valid392
  · exact recordValid_of_data section14Catalog 16 _ hnum valid393
  · exact recordValid_of_data section14Catalog 16 _ hnum valid394
  · exact recordValid_of_data section14Catalog 16 _ hnum valid395
  · exact recordValid_of_data section14Catalog 16 _ hnum valid396
  · exact recordValid_of_data section14Catalog 16 _ hnum valid397
  · exact recordValid_of_data section14Catalog 16 _ hnum valid398
  · exact recordValid_of_data section14Catalog 16 _ hnum valid399
  · exact recordValid_of_data section14Catalog 16 _ hnum valid400
  · exact recordValid_of_data section14Catalog 16 _ hnum valid401
  · exact recordValid_of_data section14Catalog 16 _ hnum valid402
  · exact recordValid_of_data section14Catalog 16 _ hnum valid403
  · exact recordValid_of_data section14Catalog 16 _ hnum valid404
  · exact recordValid_of_data section14Catalog 16 _ hnum valid405
  · exact recordValid_of_data section14Catalog 16 _ hnum valid406
  · exact recordValid_of_data section14Catalog 16 _ hnum valid407
  · exact recordValid_of_data section14Catalog 16 _ hnum valid408
  · exact recordValid_of_data section14Catalog 16 _ hnum valid409
  · exact recordValid_of_data section14Catalog 16 _ hnum valid410
  · exact recordValid_of_data section14Catalog 16 _ hnum valid411
  · exact recordValid_of_data section14Catalog 16 _ hnum valid412
  · exact recordValid_of_data section14Catalog 16 _ hnum valid413
  · exact recordValid_of_data section14Catalog 16 _ hnum valid414
  · exact recordValid_of_data section14Catalog 16 _ hnum valid415
end Section14Records_16_384_416

#print axioms solution
