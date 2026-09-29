-- Prove2me | solution 1 for Freiman.section14_s0010_records_1472_1504
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T17:09:15.204306+00:00
-- url     : https://prove2.me/submissions/92bb59f7-e523-4cdf-ac1f-52cc06d2e110

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
namespace Section14Records_10_1472_1504
private theorem valid1472 : RecordDataValid section14Catalog 10 (⟨145,(6),[9,10],[42],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1473 : RecordDataValid section14Catalog 10 (⟨145,(7),[9,10],[42],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1474 : RecordDataValid section14Catalog 10 (⟨145,(8),[9,10],[42],593⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨593,[1,4,5,6,8,9,10,12,13,16],594⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1475 : RecordDataValid section14Catalog 10 (⟨145,(9),[9,10],[42],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1476 : RecordDataValid section14Catalog 10 (⟨145,(10),[9,10],[42],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1477 : RecordDataValid section14Catalog 10 (⟨145,(11),[9,10],[42],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1478 : RecordDataValid section14Catalog 10 (⟨145,(12),[9,10],[42],601⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨601,[1,4,5,6,8,9,10,12,13,16],602⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1479 : RecordDataValid section14Catalog 10 (⟨145,(13),[9,10],[42],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1480 : RecordDataValid section14Catalog 10 (⟨145,(14),[9,10],[42],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1481 : RecordDataValid section14Catalog 10 (⟨145,(15),[9,10],[42],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1482 : RecordDataValid section14Catalog 10 (⟨146,(0),[10],[42],605⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨605,[1,5,6,10,13],606⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1483 : RecordDataValid section14Catalog 10 (⟨146,(1),[10],[42],606⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨606,[1,5,6,10,13],607⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1484 : RecordDataValid section14Catalog 10 (⟨146,(2),[9,10],[42],607⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1485 : RecordDataValid section14Catalog 10 (⟨146,(3),[10],[42],608⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨608,[1,5,6,10,13],609⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1486 : RecordDataValid section14Catalog 10 (⟨146,(4),[9,10],[42],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1487 : RecordDataValid section14Catalog 10 (⟨146,(5),[9,10],[42],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1488 : RecordDataValid section14Catalog 10 (⟨146,(6),[9,10],[42],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1489 : RecordDataValid section14Catalog 10 (⟨146,(7),[9,10],[42],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1490 : RecordDataValid section14Catalog 10 (⟨146,(8),[9,10],[42],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1491 : RecordDataValid section14Catalog 10 (⟨146,(9),[9,10],[42],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1492 : RecordDataValid section14Catalog 10 (⟨146,(10),[9,10],[42],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1493 : RecordDataValid section14Catalog 10 (⟨146,(11),[9,10],[42],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1494 : RecordDataValid section14Catalog 10 (⟨146,(12),[9,10],[42],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1495 : RecordDataValid section14Catalog 10 (⟨146,(13),[9,10],[42],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1496 : RecordDataValid section14Catalog 10 (⟨146,(14),[9,10],[42],619⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1497 : RecordDataValid section14Catalog 10 (⟨146,(15),[9,10],[42],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1498 : RecordDataValid section14Catalog 10 (⟨150,(0),[9,10],[42],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1499 : RecordDataValid section14Catalog 10 (⟨150,(1),[9,10],[42],621⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1500 : RecordDataValid section14Catalog 10 (⟨150,(2),[9,10],[42],622⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨622,[1,4,5,6,8,9,10,12],623⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1501 : RecordDataValid section14Catalog 10 (⟨150,(3),[9,10],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1502 : RecordDataValid section14Catalog 10 (⟨150,(4),[9,10],[42],622⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨622,[1,4,5,6,8,9,10,12],623⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1503 : RecordDataValid section14Catalog 10 (⟨150,(5),[9,10],[42],387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1472).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1472).take 32 = [⟨145,(6),[9,10],[42],599⟩,⟨145,(7),[9,10],[42],600⟩,⟨145,(8),[9,10],[42],593⟩,⟨145,(9),[9,10],[42],594⟩,⟨145,(10),[9,10],[42],595⟩,⟨145,(11),[9,10],[42],596⟩,⟨145,(12),[9,10],[42],601⟩,⟨145,(13),[9,10],[42],602⟩,⟨145,(14),[9,10],[42],603⟩,⟨145,(15),[9,10],[42],604⟩,⟨146,(0),[10],[42],605⟩,⟨146,(1),[10],[42],606⟩,⟨146,(2),[9,10],[42],607⟩,⟨146,(3),[10],[42],608⟩,⟨146,(4),[9,10],[42],609⟩,⟨146,(5),[9,10],[42],610⟩,⟨146,(6),[9,10],[42],611⟩,⟨146,(7),[9,10],[42],612⟩,⟨146,(8),[9,10],[42],613⟩,⟨146,(9),[9,10],[42],614⟩,⟨146,(10),[9,10],[42],615⟩,⟨146,(11),[9,10],[42],616⟩,⟨146,(12),[9,10],[42],617⟩,⟨146,(13),[9,10],[42],618⟩,⟨146,(14),[9,10],[42],619⟩,⟨146,(15),[9,10],[42],620⟩,⟨150,(0),[9,10],[42],387⟩,⟨150,(1),[9,10],[42],621⟩,⟨150,(2),[9,10],[42],622⟩,⟨150,(3),[9,10],[42],101⟩,⟨150,(4),[9,10],[42],622⟩,⟨150,(5),[9,10],[42],387⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1472
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1473
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1474
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1475
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1476
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1477
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1478
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1479
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1480
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1481
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1482
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1483
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1484
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1485
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1486
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1487
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1488
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1489
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1490
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1491
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1492
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1493
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1494
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1495
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1496
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1497
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1498
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1499
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1500
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1501
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1502
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1503
end Section14Records_10_1472_1504

#print axioms solution
