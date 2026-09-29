-- Prove2me | solution 1 for Freiman.section14_s0016_records_0480_0512
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T00:45:33.873036+00:00
-- url     : https://prove2.me/submissions/9bc46910-34b0-4d02-8a6a-5253d6add1bb

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
namespace Section14Records_16_480_512
private theorem valid480 : RecordDataValid section14Catalog 16 (⟨104,(11),[4,8,12,16],[10],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid481 : RecordDataValid section14Catalog 16 (⟨104,(12),[4,8,12,16],[10],438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨438,[1,4,5,6,8,9,10,12,13,16],439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid482 : RecordDataValid section14Catalog 16 (⟨104,(13),[4,8,12,16],[10],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid483 : RecordDataValid section14Catalog 16 (⟨104,(14),[4,8,12,16],[10],439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨439,[1,4,5,6,8,9,10,12,13,16],440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid484 : RecordDataValid section14Catalog 16 (⟨104,(15),[4,8,12,16],[10],436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨436,[1,4,5,6,8,9,10,12,13,16],437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid485 : RecordDataValid section14Catalog 16 (⟨104,(16),[4,8,12,16],[10],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid486 : RecordDataValid section14Catalog 16 (⟨104,(17),[4,8,12,16],[10],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid487 : RecordDataValid section14Catalog 16 (⟨104,(18),[4,8,12,16],[10],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid488 : RecordDataValid section14Catalog 16 (⟨104,(19),[4,8,12,16],[10],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid489 : RecordDataValid section14Catalog 16 (⟨104,(20),[4,8,12,16],[10],436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨436,[1,4,5,6,8,9,10,12,13,16],437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid490 : RecordDataValid section14Catalog 16 (⟨104,(21),[4,8,12,16],[10],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid491 : RecordDataValid section14Catalog 16 (⟨104,(22),[4,8,12,16],[10],438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨438,[1,4,5,6,8,9,10,12,13,16],439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid492 : RecordDataValid section14Catalog 16 (⟨104,(23),[4,8,12,16],[10],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid493 : RecordDataValid section14Catalog 16 (⟨104,(24),[4,8,12,16],[10],439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨439,[1,4,5,6,8,9,10,12,13,16],440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid494 : RecordDataValid section14Catalog 16 (⟨106,(0),[4,8,12,16],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid495 : RecordDataValid section14Catalog 16 (⟨106,(1),[4,8,12,16],[10],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid496 : RecordDataValid section14Catalog 16 (⟨106,(2),[4,8,12,16],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid497 : RecordDataValid section14Catalog 16 (⟨106,(3),[4,8,12,16],[10],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid498 : RecordDataValid section14Catalog 16 (⟨106,(4),[4,8,12,16],[10],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid499 : RecordDataValid section14Catalog 16 (⟨106,(5),[4,8,12,16],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid500 : RecordDataValid section14Catalog 16 (⟨106,(6),[4,8,12,16],[10],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid501 : RecordDataValid section14Catalog 16 (⟨106,(7),[4,8,12,16],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid502 : RecordDataValid section14Catalog 16 (⟨106,(8),[4,8,12,16],[10],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid503 : RecordDataValid section14Catalog 16 (⟨106,(9),[4,8,12,16],[10],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid504 : RecordDataValid section14Catalog 16 (⟨106,(10),[4,8,12,16],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid505 : RecordDataValid section14Catalog 16 (⟨106,(11),[4,8,12,16],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid506 : RecordDataValid section14Catalog 16 (⟨106,(12),[4,8,12,16],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid507 : RecordDataValid section14Catalog 16 (⟨106,(13),[4,8,12,16],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid508 : RecordDataValid section14Catalog 16 (⟨106,(14),[4,8,12,16],[10],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid509 : RecordDataValid section14Catalog 16 (⟨106,(15),[4,8,12,16],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid510 : RecordDataValid section14Catalog 16 (⟨106,(16),[4,8,12,16],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid511 : RecordDataValid section14Catalog 16 (⟨106,(17),[4,8,12,16],[10],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 480).take 32 = [⟨104,(11),[4,8,12,16],[10],437⟩,⟨104,(12),[4,8,12,16],[10],438⟩,⟨104,(13),[4,8,12,16],[10],437⟩,⟨104,(14),[4,8,12,16],[10],439⟩,⟨104,(15),[4,8,12,16],[10],436⟩,⟨104,(16),[4,8,12,16],[10],440⟩,⟨104,(17),[4,8,12,16],[10],440⟩,⟨104,(18),[4,8,12,16],[10],440⟩,⟨104,(19),[4,8,12,16],[10],440⟩,⟨104,(20),[4,8,12,16],[10],436⟩,⟨104,(21),[4,8,12,16],[10],437⟩,⟨104,(22),[4,8,12,16],[10],438⟩,⟨104,(23),[4,8,12,16],[10],437⟩,⟨104,(24),[4,8,12,16],[10],439⟩,⟨106,(0),[4,8,12,16],[10],441⟩,⟨106,(1),[4,8,12,16],[10],442⟩,⟨106,(2),[4,8,12,16],[10],441⟩,⟨106,(3),[4,8,12,16],[10],443⟩,⟨106,(4),[4,8,12,16],[10],444⟩,⟨106,(5),[4,8,12,16],[10],441⟩,⟨106,(6),[4,8,12,16],[10],442⟩,⟨106,(7),[4,8,12,16],[10],441⟩,⟨106,(8),[4,8,12,16],[10],443⟩,⟨106,(9),[4,8,12,16],[10],444⟩,⟨106,(10),[4,8,12,16],[10],445⟩,⟨106,(11),[4,8,12,16],[10],445⟩,⟨106,(12),[4,8,12,16],[10],445⟩,⟨106,(13),[4,8,12,16],[10],445⟩,⟨106,(14),[4,8,12,16],[10],444⟩,⟨106,(15),[4,8,12,16],[10],446⟩,⟨106,(16),[4,8,12,16],[10],446⟩,⟨106,(17),[4,8,12,16],[10],446⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid480
  · exact recordValid_of_data section14Catalog 16 _ hnum valid481
  · exact recordValid_of_data section14Catalog 16 _ hnum valid482
  · exact recordValid_of_data section14Catalog 16 _ hnum valid483
  · exact recordValid_of_data section14Catalog 16 _ hnum valid484
  · exact recordValid_of_data section14Catalog 16 _ hnum valid485
  · exact recordValid_of_data section14Catalog 16 _ hnum valid486
  · exact recordValid_of_data section14Catalog 16 _ hnum valid487
  · exact recordValid_of_data section14Catalog 16 _ hnum valid488
  · exact recordValid_of_data section14Catalog 16 _ hnum valid489
  · exact recordValid_of_data section14Catalog 16 _ hnum valid490
  · exact recordValid_of_data section14Catalog 16 _ hnum valid491
  · exact recordValid_of_data section14Catalog 16 _ hnum valid492
  · exact recordValid_of_data section14Catalog 16 _ hnum valid493
  · exact recordValid_of_data section14Catalog 16 _ hnum valid494
  · exact recordValid_of_data section14Catalog 16 _ hnum valid495
  · exact recordValid_of_data section14Catalog 16 _ hnum valid496
  · exact recordValid_of_data section14Catalog 16 _ hnum valid497
  · exact recordValid_of_data section14Catalog 16 _ hnum valid498
  · exact recordValid_of_data section14Catalog 16 _ hnum valid499
  · exact recordValid_of_data section14Catalog 16 _ hnum valid500
  · exact recordValid_of_data section14Catalog 16 _ hnum valid501
  · exact recordValid_of_data section14Catalog 16 _ hnum valid502
  · exact recordValid_of_data section14Catalog 16 _ hnum valid503
  · exact recordValid_of_data section14Catalog 16 _ hnum valid504
  · exact recordValid_of_data section14Catalog 16 _ hnum valid505
  · exact recordValid_of_data section14Catalog 16 _ hnum valid506
  · exact recordValid_of_data section14Catalog 16 _ hnum valid507
  · exact recordValid_of_data section14Catalog 16 _ hnum valid508
  · exact recordValid_of_data section14Catalog 16 _ hnum valid509
  · exact recordValid_of_data section14Catalog 16 _ hnum valid510
  · exact recordValid_of_data section14Catalog 16 _ hnum valid511
end Section14Records_16_480_512

#print axioms solution
