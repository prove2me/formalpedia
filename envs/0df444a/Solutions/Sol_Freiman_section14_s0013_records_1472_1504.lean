-- Prove2me | solution 1 for Freiman.section14_s0013_records_1472_1504
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T12:23:53.035355+00:00
-- url     : https://prove2.me/submissions/cdf31230-f279-4cf2-aecc-9333909a83f8

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
namespace Section14Records_13_1472_1504
private theorem valid1472 : RecordDataValid section14Catalog 13 (⟨92,(3),[1,5,6,13],[170],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1473 : RecordDataValid section14Catalog 13 (⟨92,(4),[1,5,6,13],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1474 : RecordDataValid section14Catalog 13 (⟨92,(5),[1,5,6,13],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1475 : RecordDataValid section14Catalog 13 (⟨92,(6),[1,5,6,13],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1476 : RecordDataValid section14Catalog 13 (⟨92,(7),[1,5,6,13],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1477 : RecordDataValid section14Catalog 13 (⟨92,(8),[1,5,6,13],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1478 : RecordDataValid section14Catalog 13 (⟨92,(9),[1,5,6,13],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1479 : RecordDataValid section14Catalog 13 (⟨92,(10),[1,5,6,13],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1480 : RecordDataValid section14Catalog 13 (⟨92,(11),[1,5,6,13],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1481 : RecordDataValid section14Catalog 13 (⟨92,(12),[1,5,6,13],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1482 : RecordDataValid section14Catalog 13 (⟨92,(13),[1,5,6,13],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1483 : RecordDataValid section14Catalog 13 (⟨92,(14),[1,5,6,13],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1484 : RecordDataValid section14Catalog 13 (⟨92,(15),[1,5,6,13],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1485 : RecordDataValid section14Catalog 13 (⟨95,(0),[1,5,6,13],[170],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1486 : RecordDataValid section14Catalog 13 (⟨95,(1),[1,5,6,13],[170],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1487 : RecordDataValid section14Catalog 13 (⟨95,(2),[1,5,6,13],[170],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1488 : RecordDataValid section14Catalog 13 (⟨95,(3),[1,5,6,13],[170],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1489 : RecordDataValid section14Catalog 13 (⟨95,(4),[1,5,6,13],[170],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1490 : RecordDataValid section14Catalog 13 (⟨95,(5),[1,5,6,13],[170],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1491 : RecordDataValid section14Catalog 13 (⟨95,(6),[1,5,6,13],[170],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1492 : RecordDataValid section14Catalog 13 (⟨95,(7),[1,5,6,13],[170],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1493 : RecordDataValid section14Catalog 13 (⟨95,(8),[1,5,6,13],[170],414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨414,[1,4,5,6,8,9,10,12,13,16],415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1494 : RecordDataValid section14Catalog 13 (⟨95,(9),[1,5,6,13],[170],415⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨415,[1,4,5,6,8,9,10,12,13,16],416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1495 : RecordDataValid section14Catalog 13 (⟨95,(10),[1,5,6,13],[170],414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨414,[1,4,5,6,8,9,10,12,13,16],415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1496 : RecordDataValid section14Catalog 13 (⟨95,(11),[1,5,6,13],[170],416⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨416,[1,4,5,6,8,9,10,12,13,16],417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1497 : RecordDataValid section14Catalog 13 (⟨95,(12),[1,5,6,13],[170],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1498 : RecordDataValid section14Catalog 13 (⟨95,(13),[1,5,6,13],[170],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1499 : RecordDataValid section14Catalog 13 (⟨95,(14),[1,5,6,13],[170],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1500 : RecordDataValid section14Catalog 13 (⟨95,(15),[1,5,6,13],[170],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1501 : RecordDataValid section14Catalog 13 (⟨96,(0),[1,5,6,13],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1502 : RecordDataValid section14Catalog 13 (⟨96,(1),[1,5,6,13],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1503 : RecordDataValid section14Catalog 13 (⟨96,(2),[1,5,6,13],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1472).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1472).take 32 = [⟨92,(3),[1,5,6,13],[170],408⟩,⟨92,(4),[1,5,6,13],[170],409⟩,⟨92,(5),[1,5,6,13],[170],409⟩,⟨92,(6),[1,5,6,13],[170],409⟩,⟨92,(7),[1,5,6,13],[170],409⟩,⟨92,(8),[1,5,6,13],[170],410⟩,⟨92,(9),[1,5,6,13],[170],410⟩,⟨92,(10),[1,5,6,13],[170],410⟩,⟨92,(11),[1,5,6,13],[170],410⟩,⟨92,(12),[1,5,6,13],[170],411⟩,⟨92,(13),[1,5,6,13],[170],411⟩,⟨92,(14),[1,5,6,13],[170],411⟩,⟨92,(15),[1,5,6,13],[170],411⟩,⟨95,(0),[1,5,6,13],[170],412⟩,⟨95,(1),[1,5,6,13],[170],412⟩,⟨95,(2),[1,5,6,13],[170],412⟩,⟨95,(3),[1,5,6,13],[170],412⟩,⟨95,(4),[1,5,6,13],[170],413⟩,⟨95,(5),[1,5,6,13],[170],413⟩,⟨95,(6),[1,5,6,13],[170],413⟩,⟨95,(7),[1,5,6,13],[170],413⟩,⟨95,(8),[1,5,6,13],[170],414⟩,⟨95,(9),[1,5,6,13],[170],415⟩,⟨95,(10),[1,5,6,13],[170],414⟩,⟨95,(11),[1,5,6,13],[170],416⟩,⟨95,(12),[1,5,6,13],[170],417⟩,⟨95,(13),[1,5,6,13],[170],417⟩,⟨95,(14),[1,5,6,13],[170],417⟩,⟨95,(15),[1,5,6,13],[170],417⟩,⟨96,(0),[1,5,6,13],[170],418⟩,⟨96,(1),[1,5,6,13],[170],419⟩,⟨96,(2),[1,5,6,13],[170],420⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1472
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1473
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1474
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1475
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1476
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1477
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1478
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1479
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1480
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1481
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1482
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1483
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1484
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1485
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1486
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1487
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1488
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1489
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1490
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1491
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1492
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1493
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1494
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1495
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1496
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1497
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1498
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1499
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1500
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1501
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1502
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1503
end Section14Records_13_1472_1504

#print axioms solution
