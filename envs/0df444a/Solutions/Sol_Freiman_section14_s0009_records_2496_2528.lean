-- Prove2me | solution 1 for Freiman.section14_s0009_records_2496_2528
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:33:19.834133+00:00
-- url     : https://prove2.me/submissions/eab68d1f-4720-4a61-bc62-4f2ba436b090

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
namespace Section14Records_9_2496_2528
private theorem valid2496 : RecordDataValid section14Catalog 9 (⟨275,(9),[9],[42],1423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1423,[5,8,9,12],1428⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2497 : RecordDataValid section14Catalog 9 (⟨278,(0),[9],[42],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2498 : RecordDataValid section14Catalog 9 (⟨278,(1),[9],[42],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2499 : RecordDataValid section14Catalog 9 (⟨278,(2),[9],[42],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2500 : RecordDataValid section14Catalog 9 (⟨278,(3),[9],[42],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2501 : RecordDataValid section14Catalog 9 (⟨278,(4),[9],[42],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2502 : RecordDataValid section14Catalog 9 (⟨278,(5),[9],[42],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2503 : RecordDataValid section14Catalog 9 (⟨278,(6),[9],[42],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2504 : RecordDataValid section14Catalog 9 (⟨278,(7),[9],[42],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2505 : RecordDataValid section14Catalog 9 (⟨278,(8),[9],[42],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2506 : RecordDataValid section14Catalog 9 (⟨278,(9),[9],[42],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2507 : RecordDataValid section14Catalog 9 (⟨278,(10),[9],[42],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2508 : RecordDataValid section14Catalog 9 (⟨278,(11),[9],[42],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2509 : RecordDataValid section14Catalog 9 (⟨278,(12),[9],[42],1113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1113,[3,5,7,8,9,11,12,15],1117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2510 : RecordDataValid section14Catalog 9 (⟨278,(13),[9],[42],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2511 : RecordDataValid section14Catalog 9 (⟨278,(14),[9],[42],1113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1113,[3,5,7,8,9,11,12,15],1117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2512 : RecordDataValid section14Catalog 9 (⟨278,(15),[9],[42],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2513 : RecordDataValid section14Catalog 9 (⟨278,(16),[9],[42],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2514 : RecordDataValid section14Catalog 9 (⟨278,(17),[9],[42],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2515 : RecordDataValid section14Catalog 9 (⟨278,(18),[9],[42],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2516 : RecordDataValid section14Catalog 9 (⟨278,(19),[9],[42],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2517 : RecordDataValid section14Catalog 9 (⟨278,(20),[9],[42],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2518 : RecordDataValid section14Catalog 9 (⟨278,(21),[9],[42],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2519 : RecordDataValid section14Catalog 9 (⟨278,(22),[9],[42],1114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1114,[3,5,7,8,9,11,12,15],1118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2520 : RecordDataValid section14Catalog 9 (⟨278,(23),[9],[42],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2521 : RecordDataValid section14Catalog 9 (⟨278,(24),[9],[42],1114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1114,[3,5,7,8,9,11,12,15],1118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2522 : RecordDataValid section14Catalog 9 (⟨280,(0),[9],[42],1425⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1425,[5,8,9,12],1430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2523 : RecordDataValid section14Catalog 9 (⟨280,(1),[9],[42],1425⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1425,[5,8,9,12],1430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2524 : RecordDataValid section14Catalog 9 (⟨280,(2),[9],[42],1426⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1426,[5,8,9,12],1431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2525 : RecordDataValid section14Catalog 9 (⟨280,(3),[9],[42],1427⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1427,[5,8,9,12],1432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2526 : RecordDataValid section14Catalog 9 (⟨280,(4),[9],[42],1428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1428,[5,8,9,12],1433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2527 : RecordDataValid section14Catalog 9 (⟨280,(5),[9],[42],1429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1429,[5,8,9,12],1434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2496).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2496).take 32 = [⟨275,(9),[9],[42],1423⟩,⟨278,(0),[9],[42],1108⟩,⟨278,(1),[9],[42],1109⟩,⟨278,(2),[9],[42],1110⟩,⟨278,(3),[9],[42],1110⟩,⟨278,(4),[9],[42],1110⟩,⟨278,(5),[9],[42],1108⟩,⟨278,(6),[9],[42],1109⟩,⟨278,(7),[9],[42],1111⟩,⟨278,(8),[9],[42],1112⟩,⟨278,(9),[9],[42],1111⟩,⟨278,(10),[9],[42],1108⟩,⟨278,(11),[9],[42],1109⟩,⟨278,(12),[9],[42],1113⟩,⟨278,(13),[9],[42],1112⟩,⟨278,(14),[9],[42],1113⟩,⟨278,(15),[9],[42],1108⟩,⟨278,(16),[9],[42],1109⟩,⟨278,(17),[9],[42],1111⟩,⟨278,(18),[9],[42],1112⟩,⟨278,(19),[9],[42],1111⟩,⟨278,(20),[9],[42],1108⟩,⟨278,(21),[9],[42],1109⟩,⟨278,(22),[9],[42],1114⟩,⟨278,(23),[9],[42],1112⟩,⟨278,(24),[9],[42],1114⟩,⟨280,(0),[9],[42],1425⟩,⟨280,(1),[9],[42],1425⟩,⟨280,(2),[9],[42],1426⟩,⟨280,(3),[9],[42],1427⟩,⟨280,(4),[9],[42],1428⟩,⟨280,(5),[9],[42],1429⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2496
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2497
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2498
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2499
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2500
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2501
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2502
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2503
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2504
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2505
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2506
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2507
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2508
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2509
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2510
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2511
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2512
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2513
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2514
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2515
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2516
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2517
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2518
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2519
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2520
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2521
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2522
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2523
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2524
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2525
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2526
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2527
end Section14Records_9_2496_2528

#print axioms solution
