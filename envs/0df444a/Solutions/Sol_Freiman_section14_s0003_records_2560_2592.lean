-- Prove2me | solution 1 for Freiman.section14_s0003_records_2560_2592
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:50:44.426701+00:00
-- url     : https://prove2.me/submissions/26b97e07-bb04-47e0-9ea2-45f80eed681e

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
namespace Section14Records_3_2560_2592
private theorem valid2560 : RecordDataValid section14Catalog 3 (⟨466,(1),[3,7,15],[10],1201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1201,[3,5,7,8,9,11,12,15],1205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2561 : RecordDataValid section14Catalog 3 (⟨466,(2),[3,7,15],[10],1202⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1202,[3,5,7,8,9,11,12,15],1206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2562 : RecordDataValid section14Catalog 3 (⟨466,(3),[3,7,15],[10],1203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1203,[3,5,7,8,9,11,15],1207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2563 : RecordDataValid section14Catalog 3 (⟨468,(0),[3,7,15],[10],1204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1204,[3,7,11,15],1208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2564 : RecordDataValid section14Catalog 3 (⟨468,(1),[3,7,15],[10],1205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1205,[3,7,11,15],1209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2565 : RecordDataValid section14Catalog 3 (⟨468,(2),[3,7,15],[10],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2566 : RecordDataValid section14Catalog 3 (⟨468,(3),[3,7,15],[10],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2567 : RecordDataValid section14Catalog 3 (⟨468,(4),[3,7,15],[10],1208⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1208,[3,7,11,15],1212⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2568 : RecordDataValid section14Catalog 3 (⟨468,(5),[3,7,15],[10],1205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1205,[3,7,11,15],1209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2569 : RecordDataValid section14Catalog 3 (⟨468,(6),[3,7,15],[10],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2570 : RecordDataValid section14Catalog 3 (⟨468,(7),[3,7,15],[10],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2571 : RecordDataValid section14Catalog 3 (⟨468,(8),[3,7,15],[10],1204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1204,[3,7,11,15],1208⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2572 : RecordDataValid section14Catalog 3 (⟨468,(9),[3,7,15],[10],1209⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1209,[3,7,11,15],1213⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2573 : RecordDataValid section14Catalog 3 (⟨468,(10),[3,7,15],[10],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2574 : RecordDataValid section14Catalog 3 (⟨468,(11),[3,7,15],[10],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2575 : RecordDataValid section14Catalog 3 (⟨468,(12),[3,7,15],[10],1210⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1210,[3,7,11,15],1214⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2576 : RecordDataValid section14Catalog 3 (⟨468,(13),[3,7,15],[10],1205⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1205,[3,7,11,15],1209⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2577 : RecordDataValid section14Catalog 3 (⟨468,(14),[3,7,15],[10],1206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1206,[3,7,11,15],1210⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2578 : RecordDataValid section14Catalog 3 (⟨468,(15),[3,7,15],[10],1207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1207,[3,7,11,15],1211⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2579 : RecordDataValid section14Catalog 3 (⟨470,(0),[3,7,15],[10],1211⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1211,[3,5,7,8,9,11,12,15],1215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2580 : RecordDataValid section14Catalog 3 (⟨470,(1),[3,7,15],[10],1212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1212,[3,5,7,8,9,11,12,15],1216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2581 : RecordDataValid section14Catalog 3 (⟨470,(2),[3,7,15],[10],1213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1213,[3,5,7,8,9,11,12,15],1217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2582 : RecordDataValid section14Catalog 3 (⟨470,(3),[3,7,15],[10],1214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1214,[3,5,7,8,9,11,12,15],1218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2583 : RecordDataValid section14Catalog 3 (⟨470,(4),[3,7,15],[10],1215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1215,[3,5,7,8,9,11,12,15],1219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2584 : RecordDataValid section14Catalog 3 (⟨470,(5),[3,7,15],[10],1216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1216,[3,5,7,8,9,11,12,15],1220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2585 : RecordDataValid section14Catalog 3 (⟨470,(6),[3,7,15],[10],1217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1217,[3,5,7,8,9,11,12,15],1221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2586 : RecordDataValid section14Catalog 3 (⟨470,(7),[3,7,15],[10],1218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1218,[3,5,7,8,9,11,12,15],1222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2587 : RecordDataValid section14Catalog 3 (⟨470,(8),[3,7,15],[10],1219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1219,[3,7,11,15],1223⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2588 : RecordDataValid section14Catalog 3 (⟨470,(9),[3,7,15],[10],1220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1220,[3,7,11,15],1224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2589 : RecordDataValid section14Catalog 3 (⟨470,(10),[3,7,15],[10],1221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1221,[3,7,11,15],1225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2590 : RecordDataValid section14Catalog 3 (⟨470,(11),[3,7,15],[10],1222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1222,[3,7,11,15],1226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2591 : RecordDataValid section14Catalog 3 (⟨470,(12),[3,7,15],[10],1223⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1223,[3,7,11,15],1227⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2560).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2560).take 32 = [⟨466,(1),[3,7,15],[10],1201⟩,⟨466,(2),[3,7,15],[10],1202⟩,⟨466,(3),[3,7,15],[10],1203⟩,⟨468,(0),[3,7,15],[10],1204⟩,⟨468,(1),[3,7,15],[10],1205⟩,⟨468,(2),[3,7,15],[10],1206⟩,⟨468,(3),[3,7,15],[10],1207⟩,⟨468,(4),[3,7,15],[10],1208⟩,⟨468,(5),[3,7,15],[10],1205⟩,⟨468,(6),[3,7,15],[10],1206⟩,⟨468,(7),[3,7,15],[10],1207⟩,⟨468,(8),[3,7,15],[10],1204⟩,⟨468,(9),[3,7,15],[10],1209⟩,⟨468,(10),[3,7,15],[10],1206⟩,⟨468,(11),[3,7,15],[10],1207⟩,⟨468,(12),[3,7,15],[10],1210⟩,⟨468,(13),[3,7,15],[10],1205⟩,⟨468,(14),[3,7,15],[10],1206⟩,⟨468,(15),[3,7,15],[10],1207⟩,⟨470,(0),[3,7,15],[10],1211⟩,⟨470,(1),[3,7,15],[10],1212⟩,⟨470,(2),[3,7,15],[10],1213⟩,⟨470,(3),[3,7,15],[10],1214⟩,⟨470,(4),[3,7,15],[10],1215⟩,⟨470,(5),[3,7,15],[10],1216⟩,⟨470,(6),[3,7,15],[10],1217⟩,⟨470,(7),[3,7,15],[10],1218⟩,⟨470,(8),[3,7,15],[10],1219⟩,⟨470,(9),[3,7,15],[10],1220⟩,⟨470,(10),[3,7,15],[10],1221⟩,⟨470,(11),[3,7,15],[10],1222⟩,⟨470,(12),[3,7,15],[10],1223⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2560
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2561
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2562
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2563
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2564
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2565
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2566
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2567
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2568
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2569
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2570
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2571
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2572
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2573
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2574
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2575
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2576
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2577
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2578
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2579
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2580
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2581
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2582
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2583
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2584
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2585
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2586
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2587
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2588
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2589
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2590
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2591
end Section14Records_3_2560_2592

#print axioms solution
