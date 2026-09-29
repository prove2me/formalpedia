-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2432_2496
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:14:58.780315+00:00
-- url     : https://prove2.me/submissions/7f3bb182-1faf-41c8-8c9c-4c5d2046c674

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2432_2464
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2432_2464
private theorem valid2432 : RecordDataValid section14Catalog 6 (⟨167,(12),[5,6],[174],976⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨976,[3,5,6,7],980⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2433 : RecordDataValid section14Catalog 6 (⟨167,(13),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2434 : RecordDataValid section14Catalog 6 (⟨167,(13),[5,6],[174],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2435 : RecordDataValid section14Catalog 6 (⟨167,(14),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2436 : RecordDataValid section14Catalog 6 (⟨167,(14),[5,6],[174],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2437 : RecordDataValid section14Catalog 6 (⟨167,(15),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2438 : RecordDataValid section14Catalog 6 (⟨167,(15),[5,6],[174],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2439 : RecordDataValid section14Catalog 6 (⟨171,(0),[1,2,5,6,13,14],[170],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2440 : RecordDataValid section14Catalog 6 (⟨171,(0),[5,6],[174],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2441 : RecordDataValid section14Catalog 6 (⟨171,(1),[1,2,5,6,13,14],[170],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2442 : RecordDataValid section14Catalog 6 (⟨171,(1),[5,6],[174],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2443 : RecordDataValid section14Catalog 6 (⟨171,(2),[1,2,5,6,13,14],[170],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2444 : RecordDataValid section14Catalog 6 (⟨171,(2),[5,6],[174],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2445 : RecordDataValid section14Catalog 6 (⟨171,(3),[1,2,5,6,13,14],[170],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2446 : RecordDataValid section14Catalog 6 (⟨171,(3),[5,6],[174],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2447 : RecordDataValid section14Catalog 6 (⟨172,(0),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2448 : RecordDataValid section14Catalog 6 (⟨172,(0),[5,6],[174],977⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨977,[3,5,6,7],981⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2449 : RecordDataValid section14Catalog 6 (⟨172,(1),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2450 : RecordDataValid section14Catalog 6 (⟨172,(1),[5,6],[174],978⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨978,[3,5,6,7],982⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2451 : RecordDataValid section14Catalog 6 (⟨172,(2),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2452 : RecordDataValid section14Catalog 6 (⟨172,(2),[5,6],[174],979⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨979,[3,5,6,7],983⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2453 : RecordDataValid section14Catalog 6 (⟨172,(3),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2454 : RecordDataValid section14Catalog 6 (⟨172,(3),[5,6],[174],980⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨980,[3,5,6,7],984⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2455 : RecordDataValid section14Catalog 6 (⟨172,(4),[1,2,5,6,13,14],[170],432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨432,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2456 : RecordDataValid section14Catalog 6 (⟨172,(4),[5,6],[174],981⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨981,[3,5,6,7],985⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2457 : RecordDataValid section14Catalog 6 (⟨172,(5),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2458 : RecordDataValid section14Catalog 6 (⟨172,(5),[5,6],[174],978⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨978,[3,5,6,7],982⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2459 : RecordDataValid section14Catalog 6 (⟨172,(6),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2460 : RecordDataValid section14Catalog 6 (⟨172,(6),[5,6],[174],979⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨979,[3,5,6,7],983⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2461 : RecordDataValid section14Catalog 6 (⟨172,(7),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2462 : RecordDataValid section14Catalog 6 (⟨172,(7),[5,6],[174],980⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨980,[3,5,6,7],984⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2463 : RecordDataValid section14Catalog 6 (⟨172,(8),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2432_2464 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2432).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2432).take 32 = [⟨167,(12),[5,6],[174],976⟩,⟨167,(13),[1,2,5,6,13,14],[170],419⟩,⟨167,(13),[5,6],[174],972⟩,⟨167,(14),[1,2,5,6,13,14],[170],420⟩,⟨167,(14),[5,6],[174],973⟩,⟨167,(15),[1,2,5,6,13,14],[170],421⟩,⟨167,(15),[5,6],[174],974⟩,⟨171,(0),[1,2,5,6,13,14],[170],650⟩,⟨171,(0),[5,6],[174],650⟩,⟨171,(1),[1,2,5,6,13,14],[170],651⟩,⟨171,(1),[5,6],[174],651⟩,⟨171,(2),[1,2,5,6,13,14],[170],652⟩,⟨171,(2),[5,6],[174],652⟩,⟨171,(3),[1,2,5,6,13,14],[170],653⟩,⟨171,(3),[5,6],[174],653⟩,⟨172,(0),[1,2,5,6,13,14],[170],428⟩,⟨172,(0),[5,6],[174],977⟩,⟨172,(1),[1,2,5,6,13,14],[170],429⟩,⟨172,(1),[5,6],[174],978⟩,⟨172,(2),[1,2,5,6,13,14],[170],430⟩,⟨172,(2),[5,6],[174],979⟩,⟨172,(3),[1,2,5,6,13,14],[170],431⟩,⟨172,(3),[5,6],[174],980⟩,⟨172,(4),[1,2,5,6,13,14],[170],432⟩,⟨172,(4),[5,6],[174],981⟩,⟨172,(5),[1,2,5,6,13,14],[170],429⟩,⟨172,(5),[5,6],[174],978⟩,⟨172,(6),[1,2,5,6,13,14],[170],430⟩,⟨172,(6),[5,6],[174],979⟩,⟨172,(7),[1,2,5,6,13,14],[170],431⟩,⟨172,(7),[5,6],[174],980⟩,⟨172,(8),[1,2,5,6,13,14],[170],428⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2432
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2433
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2434
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2435
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2436
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2437
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2438
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2439
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2440
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2441
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2442
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2443
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2444
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2445
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2446
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2447
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2448
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2449
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2450
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2451
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2452
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2453
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2454
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2455
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2456
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2457
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2458
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2459
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2460
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2461
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2462
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2463
end Section14Records_6_2432_2464

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2432_2464


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2464_2496
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2464_2496
private theorem valid2464 : RecordDataValid section14Catalog 6 (⟨172,(8),[5,6],[174],977⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨977,[3,5,6,7],981⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2465 : RecordDataValid section14Catalog 6 (⟨172,(9),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2466 : RecordDataValid section14Catalog 6 (⟨172,(9),[5,6],[174],978⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨978,[3,5,6,7],982⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2467 : RecordDataValid section14Catalog 6 (⟨172,(10),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2468 : RecordDataValid section14Catalog 6 (⟨172,(10),[5,6],[174],979⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨979,[3,5,6,7],983⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2469 : RecordDataValid section14Catalog 6 (⟨172,(11),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2470 : RecordDataValid section14Catalog 6 (⟨172,(11),[5,6],[174],980⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨980,[3,5,6,7],984⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2471 : RecordDataValid section14Catalog 6 (⟨172,(12),[1,2,5,6,13,14],[170],433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨433,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2472 : RecordDataValid section14Catalog 6 (⟨172,(12),[5,6],[174],982⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨982,[3,5,6,7],986⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2473 : RecordDataValid section14Catalog 6 (⟨172,(13),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2474 : RecordDataValid section14Catalog 6 (⟨172,(13),[5,6],[174],978⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨978,[3,5,6,7],982⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2475 : RecordDataValid section14Catalog 6 (⟨172,(14),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2476 : RecordDataValid section14Catalog 6 (⟨172,(14),[5,6],[174],979⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨979,[3,5,6,7],983⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2477 : RecordDataValid section14Catalog 6 (⟨172,(15),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2478 : RecordDataValid section14Catalog 6 (⟨172,(15),[5,6],[174],980⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨980,[3,5,6,7],984⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2479 : RecordDataValid section14Catalog 6 (⟨175,(0),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2480 : RecordDataValid section14Catalog 6 (⟨175,(0),[5,6],[174],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2481 : RecordDataValid section14Catalog 6 (⟨175,(1),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2482 : RecordDataValid section14Catalog 6 (⟨175,(1),[5,6],[174],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2483 : RecordDataValid section14Catalog 6 (⟨175,(2),[1,2,5,6,13,14],[170],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2484 : RecordDataValid section14Catalog 6 (⟨175,(2),[5,6],[174],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2485 : RecordDataValid section14Catalog 6 (⟨175,(3),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2486 : RecordDataValid section14Catalog 6 (⟨175,(3),[5,6],[174],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2487 : RecordDataValid section14Catalog 6 (⟨175,(4),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2488 : RecordDataValid section14Catalog 6 (⟨175,(4),[5,6],[174],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2489 : RecordDataValid section14Catalog 6 (⟨175,(5),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2490 : RecordDataValid section14Catalog 6 (⟨175,(5),[5,6],[174],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2491 : RecordDataValid section14Catalog 6 (⟨175,(6),[1,2,5,6,13,14],[170],658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨658,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],659⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2492 : RecordDataValid section14Catalog 6 (⟨175,(6),[5,6],[174],658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨658,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],659⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2493 : RecordDataValid section14Catalog 6 (⟨175,(7),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2494 : RecordDataValid section14Catalog 6 (⟨175,(7),[5,6],[174],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2495 : RecordDataValid section14Catalog 6 (⟨175,(8),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2464_2496 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2464).take 32 = [⟨172,(8),[5,6],[174],977⟩,⟨172,(9),[1,2,5,6,13,14],[170],429⟩,⟨172,(9),[5,6],[174],978⟩,⟨172,(10),[1,2,5,6,13,14],[170],430⟩,⟨172,(10),[5,6],[174],979⟩,⟨172,(11),[1,2,5,6,13,14],[170],431⟩,⟨172,(11),[5,6],[174],980⟩,⟨172,(12),[1,2,5,6,13,14],[170],433⟩,⟨172,(12),[5,6],[174],982⟩,⟨172,(13),[1,2,5,6,13,14],[170],429⟩,⟨172,(13),[5,6],[174],978⟩,⟨172,(14),[1,2,5,6,13,14],[170],430⟩,⟨172,(14),[5,6],[174],979⟩,⟨172,(15),[1,2,5,6,13,14],[170],431⟩,⟨172,(15),[5,6],[174],980⟩,⟨175,(0),[1,2,5,6,13,14],[170],654⟩,⟨175,(0),[5,6],[174],654⟩,⟨175,(1),[1,2,5,6,13,14],[170],655⟩,⟨175,(1),[5,6],[174],655⟩,⟨175,(2),[1,2,5,6,13,14],[170],656⟩,⟨175,(2),[5,6],[174],656⟩,⟨175,(3),[1,2,5,6,13,14],[170],657⟩,⟨175,(3),[5,6],[174],657⟩,⟨175,(4),[1,2,5,6,13,14],[170],654⟩,⟨175,(4),[5,6],[174],654⟩,⟨175,(5),[1,2,5,6,13,14],[170],655⟩,⟨175,(5),[5,6],[174],655⟩,⟨175,(6),[1,2,5,6,13,14],[170],658⟩,⟨175,(6),[5,6],[174],658⟩,⟨175,(7),[1,2,5,6,13,14],[170],657⟩,⟨175,(7),[5,6],[174],657⟩,⟨175,(8),[1,2,5,6,13,14],[170],654⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2464
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2465
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2466
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2467
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2468
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2469
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2470
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2471
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2472
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2473
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2474
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2475
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2476
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2477
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2478
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2479
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2480
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2481
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2482
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2483
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2484
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2485
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2486
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2487
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2488
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2489
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2490
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2491
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2492
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2493
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2494
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2495
end Section14Records_6_2464_2496

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2464_2496

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2432).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2432 2464 2496 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2432_2464 hnum) (Freiman.workReverse20260919_s0006_records_2464_2496 hnum))

#print axioms solution
