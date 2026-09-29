-- Prove2me | solution 1 for Freiman.section14_s0003_records_0480_0512
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T12:27:32.148875+00:00
-- url     : https://prove2.me/submissions/91d78058-9cc1-432e-8250-4559c871744f

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
namespace Section14Records_3_480_512
private theorem valid480 : RecordDataValid section14Catalog 3 (⟨69,(17),[3,7],[9],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid481 : RecordDataValid section14Catalog 3 (⟨69,(17),[3,7,15],[11],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid482 : RecordDataValid section14Catalog 3 (⟨69,(18),[3,7],[9],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid483 : RecordDataValid section14Catalog 3 (⟨69,(18),[3,7,15],[11],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid484 : RecordDataValid section14Catalog 3 (⟨69,(19),[3,7],[9],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid485 : RecordDataValid section14Catalog 3 (⟨69,(19),[3,7,15],[11],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid486 : RecordDataValid section14Catalog 3 (⟨69,(20),[3,7],[9],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid487 : RecordDataValid section14Catalog 3 (⟨69,(20),[3,7,15],[11],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid488 : RecordDataValid section14Catalog 3 (⟨69,(21),[3,7],[9],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid489 : RecordDataValid section14Catalog 3 (⟨69,(21),[3,7,15],[11],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid490 : RecordDataValid section14Catalog 3 (⟨69,(22),[3,7],[9],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid491 : RecordDataValid section14Catalog 3 (⟨69,(22),[3,7,15],[11],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid492 : RecordDataValid section14Catalog 3 (⟨69,(23),[3,7],[9],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid493 : RecordDataValid section14Catalog 3 (⟨69,(23),[3,7,15],[11],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid494 : RecordDataValid section14Catalog 3 (⟨69,(24),[3,7],[9],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid495 : RecordDataValid section14Catalog 3 (⟨69,(24),[3,7,15],[11],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid496 : RecordDataValid section14Catalog 3 (⟨75,(0),[3,7],[9],360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨360,[1,2,3,4,5,6,7,8,9,10,12],361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid497 : RecordDataValid section14Catalog 3 (⟨75,(0),[3,7],[11],381⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨381,[1,2,3,4,5,6,7,8,9,10,11,12],382⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid498 : RecordDataValid section14Catalog 3 (⟨75,(1),[3,7],[9],361⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨361,[1,2,3,4,5,6,7,8,9,10,12],362⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid499 : RecordDataValid section14Catalog 3 (⟨75,(1),[3,7],[11],382⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨382,[1,2,3,4,5,6,7,8,9,10,11,12],383⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid500 : RecordDataValid section14Catalog 3 (⟨75,(2),[3,7],[9],362⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨362,[1,2,3,4,5,6,7,8,9,10,12],363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid501 : RecordDataValid section14Catalog 3 (⟨75,(2),[3,7],[11],383⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨383,[1,2,3,4,5,6,7,8,9,10,11,12],384⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid502 : RecordDataValid section14Catalog 3 (⟨75,(3),[3,7],[9],363⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨363,[1,2,3,4,5,6,7,8,9,10,12],364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid503 : RecordDataValid section14Catalog 3 (⟨75,(3),[3,7],[11],384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨384,[1,2,3,4,5,6,7,8,9,10,11,12],385⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid504 : RecordDataValid section14Catalog 3 (⟨80,(5),[3,7],[9,11],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid505 : RecordDataValid section14Catalog 3 (⟨80,(7),[3,7],[9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid506 : RecordDataValid section14Catalog 3 (⟨80,(7),[3,15],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid507 : RecordDataValid section14Catalog 3 (⟨80,(8),[3,7],[9],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid508 : RecordDataValid section14Catalog 3 (⟨80,(8),[3,7,15],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid509 : RecordDataValid section14Catalog 3 (⟨80,(9),[3],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid510 : RecordDataValid section14Catalog 3 (⟨80,(9),[3,7],[9],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid511 : RecordDataValid section14Catalog 3 (⟨80,(15),[3,7],[9],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 480).take 32 = [⟨69,(17),[3,7],[9],197⟩,⟨69,(17),[3,7,15],[11],379⟩,⟨69,(18),[3,7],[9],197⟩,⟨69,(18),[3,7,15],[11],379⟩,⟨69,(19),[3,7],[9],197⟩,⟨69,(19),[3,7,15],[11],379⟩,⟨69,(20),[3,7],[9],198⟩,⟨69,(20),[3,7,15],[11],198⟩,⟨69,(21),[3,7],[9],199⟩,⟨69,(21),[3,7,15],[11],271⟩,⟨69,(22),[3,7],[9],199⟩,⟨69,(22),[3,7,15],[11],380⟩,⟨69,(23),[3,7],[9],199⟩,⟨69,(23),[3,7,15],[11],380⟩,⟨69,(24),[3,7],[9],199⟩,⟨69,(24),[3,7,15],[11],380⟩,⟨75,(0),[3,7],[9],360⟩,⟨75,(0),[3,7],[11],381⟩,⟨75,(1),[3,7],[9],361⟩,⟨75,(1),[3,7],[11],382⟩,⟨75,(2),[3,7],[9],362⟩,⟨75,(2),[3,7],[11],383⟩,⟨75,(3),[3,7],[9],363⟩,⟨75,(3),[3,7],[11],384⟩,⟨80,(5),[3,7],[9,11],105⟩,⟨80,(7),[3,7],[9],3⟩,⟨80,(7),[3,15],[11],3⟩,⟨80,(8),[3,7],[9],3⟩,⟨80,(8),[3,7,15],[11],3⟩,⟨80,(9),[3],[11],3⟩,⟨80,(9),[3,7],[9],143⟩,⟨80,(15),[3,7],[9],105⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid480
  · exact recordValid_of_data section14Catalog 3 _ hnum valid481
  · exact recordValid_of_data section14Catalog 3 _ hnum valid482
  · exact recordValid_of_data section14Catalog 3 _ hnum valid483
  · exact recordValid_of_data section14Catalog 3 _ hnum valid484
  · exact recordValid_of_data section14Catalog 3 _ hnum valid485
  · exact recordValid_of_data section14Catalog 3 _ hnum valid486
  · exact recordValid_of_data section14Catalog 3 _ hnum valid487
  · exact recordValid_of_data section14Catalog 3 _ hnum valid488
  · exact recordValid_of_data section14Catalog 3 _ hnum valid489
  · exact recordValid_of_data section14Catalog 3 _ hnum valid490
  · exact recordValid_of_data section14Catalog 3 _ hnum valid491
  · exact recordValid_of_data section14Catalog 3 _ hnum valid492
  · exact recordValid_of_data section14Catalog 3 _ hnum valid493
  · exact recordValid_of_data section14Catalog 3 _ hnum valid494
  · exact recordValid_of_data section14Catalog 3 _ hnum valid495
  · exact recordValid_of_data section14Catalog 3 _ hnum valid496
  · exact recordValid_of_data section14Catalog 3 _ hnum valid497
  · exact recordValid_of_data section14Catalog 3 _ hnum valid498
  · exact recordValid_of_data section14Catalog 3 _ hnum valid499
  · exact recordValid_of_data section14Catalog 3 _ hnum valid500
  · exact recordValid_of_data section14Catalog 3 _ hnum valid501
  · exact recordValid_of_data section14Catalog 3 _ hnum valid502
  · exact recordValid_of_data section14Catalog 3 _ hnum valid503
  · exact recordValid_of_data section14Catalog 3 _ hnum valid504
  · exact recordValid_of_data section14Catalog 3 _ hnum valid505
  · exact recordValid_of_data section14Catalog 3 _ hnum valid506
  · exact recordValid_of_data section14Catalog 3 _ hnum valid507
  · exact recordValid_of_data section14Catalog 3 _ hnum valid508
  · exact recordValid_of_data section14Catalog 3 _ hnum valid509
  · exact recordValid_of_data section14Catalog 3 _ hnum valid510
  · exact recordValid_of_data section14Catalog 3 _ hnum valid511
end Section14Records_3_480_512

#print axioms solution
