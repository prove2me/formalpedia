-- Prove2me | solution 1 for Freiman.section14_s0010_records_2464_2496
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T18:04:31.370906+00:00
-- url     : https://prove2.me/submissions/8140d2eb-5835-4015-b6b6-bb6fc57ddbce

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
namespace Section14Records_10_2464_2496
private theorem valid2464 : RecordDataValid section14Catalog 10 (⟨552,(7),[9,10],[46],1660⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1660,[9,10,12],1665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2465 : RecordDataValid section14Catalog 10 (⟨552,(8),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2466 : RecordDataValid section14Catalog 10 (⟨552,(8),[9,10],[42],1659⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1659,[9,10,11,12],1664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2467 : RecordDataValid section14Catalog 10 (⟨552,(8),[9,10],[46],1662⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1662,[9,10,12],1667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2468 : RecordDataValid section14Catalog 10 (⟨552,(9),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2469 : RecordDataValid section14Catalog 10 (⟨552,(9),[9,10],[42],256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨256,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2470 : RecordDataValid section14Catalog 10 (⟨552,(9),[9,10],[46],315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨315,[1,2,4,5,6,8,9,10,12,13,14,16],316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2471 : RecordDataValid section14Catalog 10 (⟨557,(0),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2472 : RecordDataValid section14Catalog 10 (⟨557,(0),[9,10],[46],1663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1663,[9,10,11,12],1668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2473 : RecordDataValid section14Catalog 10 (⟨557,(1),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2474 : RecordDataValid section14Catalog 10 (⟨557,(1),[9,10],[46],1664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1664,[9,10,11,12],1669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2475 : RecordDataValid section14Catalog 10 (⟨557,(2),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2476 : RecordDataValid section14Catalog 10 (⟨557,(2),[9,10],[46],1663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1663,[9,10,11,12],1668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2477 : RecordDataValid section14Catalog 10 (⟨557,(3),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2478 : RecordDataValid section14Catalog 10 (⟨557,(3),[9,10],[46],1665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1665,[9,10,11,12],1670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2479 : RecordDataValid section14Catalog 10 (⟨557,(4),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2480 : RecordDataValid section14Catalog 10 (⟨557,(4),[9,10],[46],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2481 : RecordDataValid section14Catalog 10 (⟨557,(5),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2482 : RecordDataValid section14Catalog 10 (⟨557,(5),[9,10],[46],1663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1663,[9,10,11,12],1668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2483 : RecordDataValid section14Catalog 10 (⟨557,(6),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2484 : RecordDataValid section14Catalog 10 (⟨557,(6),[9,10],[46],1664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1664,[9,10,11,12],1669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2485 : RecordDataValid section14Catalog 10 (⟨557,(7),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2486 : RecordDataValid section14Catalog 10 (⟨557,(7),[9,10],[46],1663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1663,[9,10,11,12],1668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2487 : RecordDataValid section14Catalog 10 (⟨557,(8),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2488 : RecordDataValid section14Catalog 10 (⟨557,(8),[9,10],[46],1665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1665,[9,10,11,12],1670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2489 : RecordDataValid section14Catalog 10 (⟨557,(9),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2490 : RecordDataValid section14Catalog 10 (⟨557,(9),[9,10],[46],371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨371,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2491 : RecordDataValid section14Catalog 10 (⟨562,(0),[9,10],[42],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2492 : RecordDataValid section14Catalog 10 (⟨562,(1),[9,10],[42],1666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1666,[9,10,11,12],1671⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2493 : RecordDataValid section14Catalog 10 (⟨562,(2),[9,10],[42],1667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1667,[9,10,11,12],1672⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2494 : RecordDataValid section14Catalog 10 (⟨562,(3),[9,10],[42],1668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1668,[9,10,11,12],1673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2495 : RecordDataValid section14Catalog 10 (⟨562,(4),[9,10],[42],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 2464).take 32 = [⟨552,(7),[9,10],[46],1660⟩,⟨552,(8),[9,10],[38],3⟩,⟨552,(8),[9,10],[42],1659⟩,⟨552,(8),[9,10],[46],1662⟩,⟨552,(9),[9,10],[38],3⟩,⟨552,(9),[9,10],[42],256⟩,⟨552,(9),[9,10],[46],315⟩,⟨557,(0),[9,10],[38],3⟩,⟨557,(0),[9,10],[46],1663⟩,⟨557,(1),[9,10],[38],3⟩,⟨557,(1),[9,10],[46],1664⟩,⟨557,(2),[9,10],[38],3⟩,⟨557,(2),[9,10],[46],1663⟩,⟨557,(3),[9,10],[38],3⟩,⟨557,(3),[9,10],[46],1665⟩,⟨557,(4),[9,10],[38],3⟩,⟨557,(4),[9,10],[46],371⟩,⟨557,(5),[9,10],[38],3⟩,⟨557,(5),[9,10],[46],1663⟩,⟨557,(6),[9,10],[38],3⟩,⟨557,(6),[9,10],[46],1664⟩,⟨557,(7),[9,10],[38],3⟩,⟨557,(7),[9,10],[46],1663⟩,⟨557,(8),[9,10],[38],3⟩,⟨557,(8),[9,10],[46],1665⟩,⟨557,(9),[9,10],[38],3⟩,⟨557,(9),[9,10],[46],371⟩,⟨562,(0),[9,10],[42],1649⟩,⟨562,(1),[9,10],[42],1666⟩,⟨562,(2),[9,10],[42],1667⟩,⟨562,(3),[9,10],[42],1668⟩,⟨562,(4),[9,10],[42],396⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2464
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2465
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2466
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2467
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2468
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2469
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2470
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2471
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2472
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2473
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2474
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2475
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2476
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2477
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2478
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2479
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2480
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2481
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2482
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2483
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2484
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2485
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2486
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2487
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2488
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2489
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2490
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2491
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2492
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2493
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2494
  · exact recordValid_of_data section14Catalog 10 _ hnum valid2495
end Section14Records_10_2464_2496

#print axioms solution
