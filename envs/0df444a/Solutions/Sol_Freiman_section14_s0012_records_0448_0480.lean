-- Prove2me | solution 1 for Freiman.section14_s0012_records_0448_0480
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:24:52.733971+00:00
-- url     : https://prove2.me/submissions/ba60d25c-fe3d-49d0-8756-aaa150c32fa3

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
namespace Section14Records_12_448_480
private theorem valid448 : RecordDataValid section14Catalog 12 (⟨82,(-1),[4,8,12,16],[7,11,15],391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid449 : RecordDataValid section14Catalog 12 (⟨82,(-1),[4,8,12,16],[6],392⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨392,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],393⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid450 : RecordDataValid section14Catalog 12 (⟨82,(-1),[4,8,12,16],[14],629⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨629,[1,2,4,5,6,8,9,10,12,13,14,16],630⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid451 : RecordDataValid section14Catalog 12 (⟨82,(-1),[8,12],[3],391⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid452 : RecordDataValid section14Catalog 12 (⟨89,(0),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid453 : RecordDataValid section14Catalog 12 (⟨89,(1),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid454 : RecordDataValid section14Catalog 12 (⟨89,(2),[4,8,12,16],[10],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid455 : RecordDataValid section14Catalog 12 (⟨89,(3),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid456 : RecordDataValid section14Catalog 12 (⟨89,(4),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid457 : RecordDataValid section14Catalog 12 (⟨89,(5),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid458 : RecordDataValid section14Catalog 12 (⟨89,(6),[4,8,12,16],[10],404⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨404,[1,4,5,6,8,9,10,12,13,16],405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid459 : RecordDataValid section14Catalog 12 (⟨89,(7),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid460 : RecordDataValid section14Catalog 12 (⟨89,(8),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid461 : RecordDataValid section14Catalog 12 (⟨89,(9),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid462 : RecordDataValid section14Catalog 12 (⟨89,(10),[4,8,12,16],[10],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid463 : RecordDataValid section14Catalog 12 (⟨89,(11),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid464 : RecordDataValid section14Catalog 12 (⟨89,(12),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid465 : RecordDataValid section14Catalog 12 (⟨89,(13),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid466 : RecordDataValid section14Catalog 12 (⟨89,(14),[4,8,12,16],[10],405⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨405,[1,4,5,6,8,9,10,12,13,16],406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid467 : RecordDataValid section14Catalog 12 (⟨89,(15),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid468 : RecordDataValid section14Catalog 12 (⟨92,(0),[4,8,12,16],[10],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid469 : RecordDataValid section14Catalog 12 (⟨92,(1),[4,8,12,16],[10],407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid470 : RecordDataValid section14Catalog 12 (⟨92,(2),[4,8,12,16],[10],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid471 : RecordDataValid section14Catalog 12 (⟨92,(3),[4,8,12,16],[10],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid472 : RecordDataValid section14Catalog 12 (⟨92,(4),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid473 : RecordDataValid section14Catalog 12 (⟨92,(5),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid474 : RecordDataValid section14Catalog 12 (⟨92,(6),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid475 : RecordDataValid section14Catalog 12 (⟨92,(7),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid476 : RecordDataValid section14Catalog 12 (⟨92,(8),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid477 : RecordDataValid section14Catalog 12 (⟨92,(9),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid478 : RecordDataValid section14Catalog 12 (⟨92,(10),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid479 : RecordDataValid section14Catalog 12 (⟨92,(11),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 448).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 448).take 32 = [⟨82,(-1),[4,8,12,16],[7,11,15],391⟩,⟨82,(-1),[4,8,12,16],[6],392⟩,⟨82,(-1),[4,8,12,16],[14],629⟩,⟨82,(-1),[8,12],[3],391⟩,⟨89,(0),[4,8,12,16],[10],400⟩,⟨89,(1),[4,8,12,16],[10],401⟩,⟨89,(2),[4,8,12,16],[10],402⟩,⟨89,(3),[4,8,12,16],[10],403⟩,⟨89,(4),[4,8,12,16],[10],400⟩,⟨89,(5),[4,8,12,16],[10],401⟩,⟨89,(6),[4,8,12,16],[10],404⟩,⟨89,(7),[4,8,12,16],[10],403⟩,⟨89,(8),[4,8,12,16],[10],400⟩,⟨89,(9),[4,8,12,16],[10],401⟩,⟨89,(10),[4,8,12,16],[10],402⟩,⟨89,(11),[4,8,12,16],[10],403⟩,⟨89,(12),[4,8,12,16],[10],400⟩,⟨89,(13),[4,8,12,16],[10],401⟩,⟨89,(14),[4,8,12,16],[10],405⟩,⟨89,(15),[4,8,12,16],[10],403⟩,⟨92,(0),[4,8,12,16],[10],406⟩,⟨92,(1),[4,8,12,16],[10],407⟩,⟨92,(2),[4,8,12,16],[10],406⟩,⟨92,(3),[4,8,12,16],[10],408⟩,⟨92,(4),[4,8,12,16],[10],409⟩,⟨92,(5),[4,8,12,16],[10],409⟩,⟨92,(6),[4,8,12,16],[10],409⟩,⟨92,(7),[4,8,12,16],[10],409⟩,⟨92,(8),[4,8,12,16],[10],410⟩,⟨92,(9),[4,8,12,16],[10],410⟩,⟨92,(10),[4,8,12,16],[10],410⟩,⟨92,(11),[4,8,12,16],[10],410⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid448
  · exact recordValid_of_data section14Catalog 12 _ hnum valid449
  · exact recordValid_of_data section14Catalog 12 _ hnum valid450
  · exact recordValid_of_data section14Catalog 12 _ hnum valid451
  · exact recordValid_of_data section14Catalog 12 _ hnum valid452
  · exact recordValid_of_data section14Catalog 12 _ hnum valid453
  · exact recordValid_of_data section14Catalog 12 _ hnum valid454
  · exact recordValid_of_data section14Catalog 12 _ hnum valid455
  · exact recordValid_of_data section14Catalog 12 _ hnum valid456
  · exact recordValid_of_data section14Catalog 12 _ hnum valid457
  · exact recordValid_of_data section14Catalog 12 _ hnum valid458
  · exact recordValid_of_data section14Catalog 12 _ hnum valid459
  · exact recordValid_of_data section14Catalog 12 _ hnum valid460
  · exact recordValid_of_data section14Catalog 12 _ hnum valid461
  · exact recordValid_of_data section14Catalog 12 _ hnum valid462
  · exact recordValid_of_data section14Catalog 12 _ hnum valid463
  · exact recordValid_of_data section14Catalog 12 _ hnum valid464
  · exact recordValid_of_data section14Catalog 12 _ hnum valid465
  · exact recordValid_of_data section14Catalog 12 _ hnum valid466
  · exact recordValid_of_data section14Catalog 12 _ hnum valid467
  · exact recordValid_of_data section14Catalog 12 _ hnum valid468
  · exact recordValid_of_data section14Catalog 12 _ hnum valid469
  · exact recordValid_of_data section14Catalog 12 _ hnum valid470
  · exact recordValid_of_data section14Catalog 12 _ hnum valid471
  · exact recordValid_of_data section14Catalog 12 _ hnum valid472
  · exact recordValid_of_data section14Catalog 12 _ hnum valid473
  · exact recordValid_of_data section14Catalog 12 _ hnum valid474
  · exact recordValid_of_data section14Catalog 12 _ hnum valid475
  · exact recordValid_of_data section14Catalog 12 _ hnum valid476
  · exact recordValid_of_data section14Catalog 12 _ hnum valid477
  · exact recordValid_of_data section14Catalog 12 _ hnum valid478
  · exact recordValid_of_data section14Catalog 12 _ hnum valid479
end Section14Records_12_448_480

#print axioms solution
