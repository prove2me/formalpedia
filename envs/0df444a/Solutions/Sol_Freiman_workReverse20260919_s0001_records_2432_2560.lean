-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_2432_2560
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:46:05.985982+00:00
-- url     : https://prove2.me/submissions/2ea8cef2-d05e-4f23-9e6e-e703d16428ff

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2432_2464
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2432_2464
private theorem valid2432 : RecordDataValid section14Catalog 1 (⟨92,(2),[1,5,6,13],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2433 : RecordDataValid section14Catalog 1 (⟨92,(3),[1,5,6,13],[170],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2434 : RecordDataValid section14Catalog 1 (⟨92,(4),[1,5,6,13],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2435 : RecordDataValid section14Catalog 1 (⟨92,(5),[1,5,6,13],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2436 : RecordDataValid section14Catalog 1 (⟨92,(6),[1,5,6,13],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2437 : RecordDataValid section14Catalog 1 (⟨92,(7),[1,5,6,13],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2438 : RecordDataValid section14Catalog 1 (⟨92,(8),[1,5,6,13],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2439 : RecordDataValid section14Catalog 1 (⟨92,(9),[1,5,6,13],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2440 : RecordDataValid section14Catalog 1 (⟨92,(10),[1,5,6,13],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2441 : RecordDataValid section14Catalog 1 (⟨92,(11),[1,5,6,13],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2442 : RecordDataValid section14Catalog 1 (⟨92,(12),[1,5,6,13],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2443 : RecordDataValid section14Catalog 1 (⟨92,(13),[1,5,6,13],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2444 : RecordDataValid section14Catalog 1 (⟨92,(14),[1,5,6,13],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2445 : RecordDataValid section14Catalog 1 (⟨92,(15),[1,5,6,13],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2446 : RecordDataValid section14Catalog 1 (⟨95,(0),[1,5,6,13],[170],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2447 : RecordDataValid section14Catalog 1 (⟨95,(1),[1,5,6,13],[170],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2448 : RecordDataValid section14Catalog 1 (⟨95,(2),[1,5,6,13],[170],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2449 : RecordDataValid section14Catalog 1 (⟨95,(3),[1,5,6,13],[170],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2450 : RecordDataValid section14Catalog 1 (⟨95,(4),[1,5,6,13],[170],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2451 : RecordDataValid section14Catalog 1 (⟨95,(5),[1,5,6,13],[170],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2452 : RecordDataValid section14Catalog 1 (⟨95,(6),[1,5,6,13],[170],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2453 : RecordDataValid section14Catalog 1 (⟨95,(7),[1,5,6,13],[170],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2454 : RecordDataValid section14Catalog 1 (⟨95,(8),[1,5,6,13],[170],414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨414,[1,4,5,6,8,9,10,12,13,16],415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2455 : RecordDataValid section14Catalog 1 (⟨95,(9),[1,5,6,13],[170],415⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨415,[1,4,5,6,8,9,10,12,13,16],416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2456 : RecordDataValid section14Catalog 1 (⟨95,(10),[1,5,6,13],[170],414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨414,[1,4,5,6,8,9,10,12,13,16],415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2457 : RecordDataValid section14Catalog 1 (⟨95,(11),[1,5,6,13],[170],416⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨416,[1,4,5,6,8,9,10,12,13,16],417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2458 : RecordDataValid section14Catalog 1 (⟨95,(12),[1,5,6,13],[170],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2459 : RecordDataValid section14Catalog 1 (⟨95,(13),[1,5,6,13],[170],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2460 : RecordDataValid section14Catalog 1 (⟨95,(14),[1,5,6,13],[170],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2461 : RecordDataValid section14Catalog 1 (⟨95,(15),[1,5,6,13],[170],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2462 : RecordDataValid section14Catalog 1 (⟨96,(0),[1,5,6,13],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2463 : RecordDataValid section14Catalog 1 (⟨96,(1),[1,5,6,13],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2432_2464 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2432).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2432).take 32 = [⟨92,(2),[1,5,6,13],[170],406⟩,⟨92,(3),[1,5,6,13],[170],408⟩,⟨92,(4),[1,5,6,13],[170],409⟩,⟨92,(5),[1,5,6,13],[170],409⟩,⟨92,(6),[1,5,6,13],[170],409⟩,⟨92,(7),[1,5,6,13],[170],409⟩,⟨92,(8),[1,5,6,13],[170],410⟩,⟨92,(9),[1,5,6,13],[170],410⟩,⟨92,(10),[1,5,6,13],[170],410⟩,⟨92,(11),[1,5,6,13],[170],410⟩,⟨92,(12),[1,5,6,13],[170],411⟩,⟨92,(13),[1,5,6,13],[170],411⟩,⟨92,(14),[1,5,6,13],[170],411⟩,⟨92,(15),[1,5,6,13],[170],411⟩,⟨95,(0),[1,5,6,13],[170],412⟩,⟨95,(1),[1,5,6,13],[170],412⟩,⟨95,(2),[1,5,6,13],[170],412⟩,⟨95,(3),[1,5,6,13],[170],412⟩,⟨95,(4),[1,5,6,13],[170],413⟩,⟨95,(5),[1,5,6,13],[170],413⟩,⟨95,(6),[1,5,6,13],[170],413⟩,⟨95,(7),[1,5,6,13],[170],413⟩,⟨95,(8),[1,5,6,13],[170],414⟩,⟨95,(9),[1,5,6,13],[170],415⟩,⟨95,(10),[1,5,6,13],[170],414⟩,⟨95,(11),[1,5,6,13],[170],416⟩,⟨95,(12),[1,5,6,13],[170],417⟩,⟨95,(13),[1,5,6,13],[170],417⟩,⟨95,(14),[1,5,6,13],[170],417⟩,⟨95,(15),[1,5,6,13],[170],417⟩,⟨96,(0),[1,5,6,13],[170],418⟩,⟨96,(1),[1,5,6,13],[170],419⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2432
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2433
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2434
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2435
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2436
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2437
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2438
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2439
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2440
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2441
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2442
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2443
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2444
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2445
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2446
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2447
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2448
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2449
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2450
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2451
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2452
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2453
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2454
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2455
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2456
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2457
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2458
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2459
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2460
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2461
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2462
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2463
end Section14Records_1_2432_2464

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2432_2464


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2464_2496
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2464_2496
private theorem valid2464 : RecordDataValid section14Catalog 1 (⟨96,(2),[1,5,6,13],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2465 : RecordDataValid section14Catalog 1 (⟨96,(3),[1,5,6,13],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2466 : RecordDataValid section14Catalog 1 (⟨96,(4),[1,5,6,13],[170],422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2467 : RecordDataValid section14Catalog 1 (⟨96,(5),[1,5,6,13],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2468 : RecordDataValid section14Catalog 1 (⟨96,(6),[1,5,6,13],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2469 : RecordDataValid section14Catalog 1 (⟨96,(7),[1,5,6,13],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2470 : RecordDataValid section14Catalog 1 (⟨96,(8),[1,5,6,13],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2471 : RecordDataValid section14Catalog 1 (⟨96,(9),[1,5,6,13],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2472 : RecordDataValid section14Catalog 1 (⟨96,(10),[1,5,6,13],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2473 : RecordDataValid section14Catalog 1 (⟨96,(11),[1,5,6,13],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2474 : RecordDataValid section14Catalog 1 (⟨96,(12),[1,5,6,13],[170],423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨423,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2475 : RecordDataValid section14Catalog 1 (⟨96,(13),[1,5,6,13],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2476 : RecordDataValid section14Catalog 1 (⟨96,(14),[1,5,6,13],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2477 : RecordDataValid section14Catalog 1 (⟨96,(15),[1,5,6,13],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2478 : RecordDataValid section14Catalog 1 (⟨100,(0),[1,5,6,13],[170],424⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨424,[1,4,5,6,8,9,10,12,13,16],425⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2479 : RecordDataValid section14Catalog 1 (⟨100,(1),[1,5,6,13],[170],425⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨425,[1,4,5,6,8,9,10,12,13,16],426⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2480 : RecordDataValid section14Catalog 1 (⟨100,(2),[1,5,6,13],[170],426⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨426,[1,4,5,6,8,9,10,12,13,16],427⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2481 : RecordDataValid section14Catalog 1 (⟨100,(3),[1,5,6,13],[170],427⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨427,[1,4,5,6,8,9,10,12,13,16],428⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2482 : RecordDataValid section14Catalog 1 (⟨101,(0),[1,5,6,13],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2483 : RecordDataValid section14Catalog 1 (⟨101,(1),[1,5,6,13],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2484 : RecordDataValid section14Catalog 1 (⟨101,(2),[1,5,6,13],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2485 : RecordDataValid section14Catalog 1 (⟨101,(3),[1,5,6,13],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2486 : RecordDataValid section14Catalog 1 (⟨101,(4),[1,5,6,13],[170],432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨432,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2487 : RecordDataValid section14Catalog 1 (⟨101,(5),[1,5,6,13],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2488 : RecordDataValid section14Catalog 1 (⟨101,(6),[1,5,6,13],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2489 : RecordDataValid section14Catalog 1 (⟨101,(7),[1,5,6,13],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2490 : RecordDataValid section14Catalog 1 (⟨101,(8),[1,5,6,13],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2491 : RecordDataValid section14Catalog 1 (⟨101,(9),[1,5,6,13],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2492 : RecordDataValid section14Catalog 1 (⟨101,(10),[1,5,6,13],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2493 : RecordDataValid section14Catalog 1 (⟨101,(11),[1,5,6,13],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2494 : RecordDataValid section14Catalog 1 (⟨101,(12),[1,5,6,13],[170],433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨433,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2495 : RecordDataValid section14Catalog 1 (⟨101,(13),[1,5,6,13],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2464_2496 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2464).take 32 = [⟨96,(2),[1,5,6,13],[170],420⟩,⟨96,(3),[1,5,6,13],[170],421⟩,⟨96,(4),[1,5,6,13],[170],422⟩,⟨96,(5),[1,5,6,13],[170],419⟩,⟨96,(6),[1,5,6,13],[170],420⟩,⟨96,(7),[1,5,6,13],[170],421⟩,⟨96,(8),[1,5,6,13],[170],418⟩,⟨96,(9),[1,5,6,13],[170],419⟩,⟨96,(10),[1,5,6,13],[170],420⟩,⟨96,(11),[1,5,6,13],[170],421⟩,⟨96,(12),[1,5,6,13],[170],423⟩,⟨96,(13),[1,5,6,13],[170],419⟩,⟨96,(14),[1,5,6,13],[170],420⟩,⟨96,(15),[1,5,6,13],[170],421⟩,⟨100,(0),[1,5,6,13],[170],424⟩,⟨100,(1),[1,5,6,13],[170],425⟩,⟨100,(2),[1,5,6,13],[170],426⟩,⟨100,(3),[1,5,6,13],[170],427⟩,⟨101,(0),[1,5,6,13],[170],428⟩,⟨101,(1),[1,5,6,13],[170],429⟩,⟨101,(2),[1,5,6,13],[170],430⟩,⟨101,(3),[1,5,6,13],[170],431⟩,⟨101,(4),[1,5,6,13],[170],432⟩,⟨101,(5),[1,5,6,13],[170],429⟩,⟨101,(6),[1,5,6,13],[170],430⟩,⟨101,(7),[1,5,6,13],[170],431⟩,⟨101,(8),[1,5,6,13],[170],428⟩,⟨101,(9),[1,5,6,13],[170],429⟩,⟨101,(10),[1,5,6,13],[170],430⟩,⟨101,(11),[1,5,6,13],[170],431⟩,⟨101,(12),[1,5,6,13],[170],433⟩,⟨101,(13),[1,5,6,13],[170],429⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2464
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2465
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2466
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2467
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2468
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2469
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2470
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2471
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2472
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2473
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2474
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2475
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2476
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2477
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2478
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2479
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2480
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2481
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2482
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2483
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2484
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2485
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2486
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2487
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2488
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2489
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2490
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2491
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2492
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2493
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2494
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2495
end Section14Records_1_2464_2496

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2464_2496


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2496_2528
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2496_2528
private theorem valid2496 : RecordDataValid section14Catalog 1 (⟨101,(14),[1,5,6,13],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2497 : RecordDataValid section14Catalog 1 (⟨101,(15),[1,5,6,13],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2498 : RecordDataValid section14Catalog 1 (⟨104,(0),[1,5,6,13],[170],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2499 : RecordDataValid section14Catalog 1 (⟨104,(1),[1,5,6,13],[170],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2500 : RecordDataValid section14Catalog 1 (⟨104,(2),[1,5,6,13],[170],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2501 : RecordDataValid section14Catalog 1 (⟨104,(3),[1,5,6,13],[170],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2502 : RecordDataValid section14Catalog 1 (⟨104,(4),[1,5,6,13],[170],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2503 : RecordDataValid section14Catalog 1 (⟨104,(5),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2504 : RecordDataValid section14Catalog 1 (⟨104,(6),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2505 : RecordDataValid section14Catalog 1 (⟨104,(7),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2506 : RecordDataValid section14Catalog 1 (⟨104,(8),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2507 : RecordDataValid section14Catalog 1 (⟨104,(9),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2508 : RecordDataValid section14Catalog 1 (⟨104,(10),[1,5,6,13],[170],436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨436,[1,4,5,6,8,9,10,12,13,16],437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2509 : RecordDataValid section14Catalog 1 (⟨104,(11),[1,5,6,13],[170],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2510 : RecordDataValid section14Catalog 1 (⟨104,(12),[1,5,6,13],[170],438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨438,[1,4,5,6,8,9,10,12,13,16],439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2511 : RecordDataValid section14Catalog 1 (⟨104,(13),[1,5,6,13],[170],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2512 : RecordDataValid section14Catalog 1 (⟨104,(14),[1,5,6,13],[170],439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨439,[1,4,5,6,8,9,10,12,13,16],440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2513 : RecordDataValid section14Catalog 1 (⟨104,(15),[1,5,6,13],[170],436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨436,[1,4,5,6,8,9,10,12,13,16],437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2514 : RecordDataValid section14Catalog 1 (⟨104,(16),[1,5,6,13],[170],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2515 : RecordDataValid section14Catalog 1 (⟨104,(17),[1,5,6,13],[170],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2516 : RecordDataValid section14Catalog 1 (⟨104,(18),[1,5,6,13],[170],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2517 : RecordDataValid section14Catalog 1 (⟨104,(19),[1,5,6,13],[170],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2518 : RecordDataValid section14Catalog 1 (⟨104,(20),[1,5,6,13],[170],436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨436,[1,4,5,6,8,9,10,12,13,16],437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2519 : RecordDataValid section14Catalog 1 (⟨104,(21),[1,5,6,13],[170],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2520 : RecordDataValid section14Catalog 1 (⟨104,(22),[1,5,6,13],[170],438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨438,[1,4,5,6,8,9,10,12,13,16],439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2521 : RecordDataValid section14Catalog 1 (⟨104,(23),[1,5,6,13],[170],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2522 : RecordDataValid section14Catalog 1 (⟨104,(24),[1,5,6,13],[170],439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨439,[1,4,5,6,8,9,10,12,13,16],440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2523 : RecordDataValid section14Catalog 1 (⟨106,(0),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2524 : RecordDataValid section14Catalog 1 (⟨106,(1),[1,5,6,13],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2525 : RecordDataValid section14Catalog 1 (⟨106,(2),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2526 : RecordDataValid section14Catalog 1 (⟨106,(3),[1,5,6,13],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2527 : RecordDataValid section14Catalog 1 (⟨106,(4),[1,5,6,13],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2496_2528 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2496).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2496).take 32 = [⟨101,(14),[1,5,6,13],[170],430⟩,⟨101,(15),[1,5,6,13],[170],431⟩,⟨104,(0),[1,5,6,13],[170],434⟩,⟨104,(1),[1,5,6,13],[170],434⟩,⟨104,(2),[1,5,6,13],[170],434⟩,⟨104,(3),[1,5,6,13],[170],434⟩,⟨104,(4),[1,5,6,13],[170],434⟩,⟨104,(5),[1,5,6,13],[170],435⟩,⟨104,(6),[1,5,6,13],[170],435⟩,⟨104,(7),[1,5,6,13],[170],435⟩,⟨104,(8),[1,5,6,13],[170],435⟩,⟨104,(9),[1,5,6,13],[170],435⟩,⟨104,(10),[1,5,6,13],[170],436⟩,⟨104,(11),[1,5,6,13],[170],437⟩,⟨104,(12),[1,5,6,13],[170],438⟩,⟨104,(13),[1,5,6,13],[170],437⟩,⟨104,(14),[1,5,6,13],[170],439⟩,⟨104,(15),[1,5,6,13],[170],436⟩,⟨104,(16),[1,5,6,13],[170],440⟩,⟨104,(17),[1,5,6,13],[170],440⟩,⟨104,(18),[1,5,6,13],[170],440⟩,⟨104,(19),[1,5,6,13],[170],440⟩,⟨104,(20),[1,5,6,13],[170],436⟩,⟨104,(21),[1,5,6,13],[170],437⟩,⟨104,(22),[1,5,6,13],[170],438⟩,⟨104,(23),[1,5,6,13],[170],437⟩,⟨104,(24),[1,5,6,13],[170],439⟩,⟨106,(0),[1,5,6,13],[170],441⟩,⟨106,(1),[1,5,6,13],[170],442⟩,⟨106,(2),[1,5,6,13],[170],441⟩,⟨106,(3),[1,5,6,13],[170],443⟩,⟨106,(4),[1,5,6,13],[170],444⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2496
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2497
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2498
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2499
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2500
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2501
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2502
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2503
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2504
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2505
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2506
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2507
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2508
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2509
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2510
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2511
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2512
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2513
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2514
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2515
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2516
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2517
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2518
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2519
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2520
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2521
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2522
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2523
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2524
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2525
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2526
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2527
end Section14Records_1_2496_2528

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2496_2528


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2528_2560
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_2528_2560
private theorem valid2528 : RecordDataValid section14Catalog 1 (⟨106,(5),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2529 : RecordDataValid section14Catalog 1 (⟨106,(6),[1,5,6,13],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2530 : RecordDataValid section14Catalog 1 (⟨106,(7),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2531 : RecordDataValid section14Catalog 1 (⟨106,(8),[1,5,6,13],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2532 : RecordDataValid section14Catalog 1 (⟨106,(9),[1,5,6,13],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2533 : RecordDataValid section14Catalog 1 (⟨106,(10),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2534 : RecordDataValid section14Catalog 1 (⟨106,(11),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2535 : RecordDataValid section14Catalog 1 (⟨106,(12),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2536 : RecordDataValid section14Catalog 1 (⟨106,(13),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2537 : RecordDataValid section14Catalog 1 (⟨106,(14),[1,5,6,13],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2538 : RecordDataValid section14Catalog 1 (⟨106,(15),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2539 : RecordDataValid section14Catalog 1 (⟨106,(16),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2540 : RecordDataValid section14Catalog 1 (⟨106,(17),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2541 : RecordDataValid section14Catalog 1 (⟨106,(18),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2542 : RecordDataValid section14Catalog 1 (⟨106,(19),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2543 : RecordDataValid section14Catalog 1 (⟨106,(20),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2544 : RecordDataValid section14Catalog 1 (⟨106,(21),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2545 : RecordDataValid section14Catalog 1 (⟨106,(22),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2546 : RecordDataValid section14Catalog 1 (⟨106,(23),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2547 : RecordDataValid section14Catalog 1 (⟨106,(24),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2548 : RecordDataValid section14Catalog 1 (⟨109,(0),[1,5,6,13],[170],448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨448,[1,4,5,6,8,9,10,12,13,16],449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2549 : RecordDataValid section14Catalog 1 (⟨109,(1),[1,5,6,13],[170],448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨448,[1,4,5,6,8,9,10,12,13,16],449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2550 : RecordDataValid section14Catalog 1 (⟨109,(2),[1,5,6,13],[170],449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨449,[1,4,5,6,8,9,10,12,13,16],450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2551 : RecordDataValid section14Catalog 1 (⟨109,(3),[1,5,6,13],[170],449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨449,[1,4,5,6,8,9,10,12,13,16],450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2552 : RecordDataValid section14Catalog 1 (⟨109,(4),[1,5,6,13],[170],450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2553 : RecordDataValid section14Catalog 1 (⟨109,(5),[1,5,6,13],[170],451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨451,[1,4,5,6,8,9,10,12,13,16],452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2554 : RecordDataValid section14Catalog 1 (⟨109,(6),[1,5,6,13],[170],450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2555 : RecordDataValid section14Catalog 1 (⟨109,(7),[1,5,6,13],[170],452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨452,[1,4,5,6,8,9,10,12,13,16],453⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2556 : RecordDataValid section14Catalog 1 (⟨109,(8),[1,5,6,13],[170],450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2557 : RecordDataValid section14Catalog 1 (⟨109,(9),[1,5,6,13],[170],451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨451,[1,4,5,6,8,9,10,12,13,16],452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2558 : RecordDataValid section14Catalog 1 (⟨111,(0),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2559 : RecordDataValid section14Catalog 1 (⟨111,(1),[1,5,6,13],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_2528_2560 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2528).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2528).take 32 = [⟨106,(5),[1,5,6,13],[170],441⟩,⟨106,(6),[1,5,6,13],[170],442⟩,⟨106,(7),[1,5,6,13],[170],441⟩,⟨106,(8),[1,5,6,13],[170],443⟩,⟨106,(9),[1,5,6,13],[170],444⟩,⟨106,(10),[1,5,6,13],[170],445⟩,⟨106,(11),[1,5,6,13],[170],445⟩,⟨106,(12),[1,5,6,13],[170],445⟩,⟨106,(13),[1,5,6,13],[170],445⟩,⟨106,(14),[1,5,6,13],[170],444⟩,⟨106,(15),[1,5,6,13],[170],446⟩,⟨106,(16),[1,5,6,13],[170],446⟩,⟨106,(17),[1,5,6,13],[170],446⟩,⟨106,(18),[1,5,6,13],[170],446⟩,⟨106,(19),[1,5,6,13],[170],446⟩,⟨106,(20),[1,5,6,13],[170],447⟩,⟨106,(21),[1,5,6,13],[170],447⟩,⟨106,(22),[1,5,6,13],[170],447⟩,⟨106,(23),[1,5,6,13],[170],447⟩,⟨106,(24),[1,5,6,13],[170],447⟩,⟨109,(0),[1,5,6,13],[170],448⟩,⟨109,(1),[1,5,6,13],[170],448⟩,⟨109,(2),[1,5,6,13],[170],449⟩,⟨109,(3),[1,5,6,13],[170],449⟩,⟨109,(4),[1,5,6,13],[170],450⟩,⟨109,(5),[1,5,6,13],[170],451⟩,⟨109,(6),[1,5,6,13],[170],450⟩,⟨109,(7),[1,5,6,13],[170],452⟩,⟨109,(8),[1,5,6,13],[170],450⟩,⟨109,(9),[1,5,6,13],[170],451⟩,⟨111,(0),[1,5,6,13],[170],453⟩,⟨111,(1),[1,5,6,13],[170],454⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2528
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2529
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2530
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2531
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2532
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2533
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2534
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2535
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2536
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2537
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2538
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2539
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2540
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2541
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2542
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2543
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2544
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2545
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2546
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2547
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2548
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2549
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2550
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2551
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2552
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2553
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2554
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2555
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2556
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2557
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2558
  · exact recordValid_of_data section14Catalog 1 _ hnum valid2559
end Section14Records_1_2528_2560

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_2528_2560

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 2432).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 2432 2496 2560 (by decide) (by decide) (all_of_interval_split P xs 2432 2464 2496 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_2432_2464 hnum) (Freiman.workReverse20260919_s0001_records_2464_2496 hnum)) (all_of_interval_split P xs 2496 2528 2560 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_2496_2528 hnum) (Freiman.workReverse20260919_s0001_records_2528_2560 hnum)))

#print axioms solution
