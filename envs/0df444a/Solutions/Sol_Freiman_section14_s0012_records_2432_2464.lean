-- Prove2me | solution 1 for Freiman.section14_s0012_records_2432_2464
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:32:59.35577+00:00
-- url     : https://prove2.me/submissions/4c4996c2-1192-4870-b63b-2131b8d55fce

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
namespace Section14Records_12_2432_2464
private theorem valid2432 : RecordDataValid section14Catalog 12 (⟨532,(4),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2433 : RecordDataValid section14Catalog 12 (⟨532,(5),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2434 : RecordDataValid section14Catalog 12 (⟨532,(6),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2435 : RecordDataValid section14Catalog 12 (⟨532,(7),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2436 : RecordDataValid section14Catalog 12 (⟨532,(8),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2437 : RecordDataValid section14Catalog 12 (⟨532,(9),[8,12],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2438 : RecordDataValid section14Catalog 12 (⟨537,(0),[12],[10],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2439 : RecordDataValid section14Catalog 12 (⟨537,(1),[12],[10],1650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1650,[9,10,11,12],1655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2440 : RecordDataValid section14Catalog 12 (⟨537,(2),[12],[10],1651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1651,[9,10,11,12],1656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2441 : RecordDataValid section14Catalog 12 (⟨537,(3),[12],[10],1652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1652,[9,10,11,12],1657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2442 : RecordDataValid section14Catalog 12 (⟨537,(4),[12],[10],17⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2443 : RecordDataValid section14Catalog 12 (⟨537,(5),[12],[10],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2444 : RecordDataValid section14Catalog 12 (⟨537,(6),[12],[10],1650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1650,[9,10,11,12],1655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2445 : RecordDataValid section14Catalog 12 (⟨537,(7),[12],[10],1651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1651,[9,10,11,12],1656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2446 : RecordDataValid section14Catalog 12 (⟨537,(8),[12],[10],1652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1652,[9,10,11,12],1657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2447 : RecordDataValid section14Catalog 12 (⟨537,(9),[12],[10],17⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2448 : RecordDataValid section14Catalog 12 (⟨542,(0),[12],[10],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2449 : RecordDataValid section14Catalog 12 (⟨542,(1),[12],[10],46⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2450 : RecordDataValid section14Catalog 12 (⟨542,(2),[12],[10],42⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2451 : RecordDataValid section14Catalog 12 (⟨542,(3),[12],[10],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2452 : RecordDataValid section14Catalog 12 (⟨542,(4),[12],[10],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2453 : RecordDataValid section14Catalog 12 (⟨542,(5),[12],[10],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2454 : RecordDataValid section14Catalog 12 (⟨542,(6),[12],[10],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2455 : RecordDataValid section14Catalog 12 (⟨542,(7),[12],[10],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2456 : RecordDataValid section14Catalog 12 (⟨542,(8),[12],[10],43⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2457 : RecordDataValid section14Catalog 12 (⟨542,(9),[12],[10],44⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2458 : RecordDataValid section14Catalog 12 (⟨547,(0),[12],[2,6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2459 : RecordDataValid section14Catalog 12 (⟨547,(1),[12],[2,6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2460 : RecordDataValid section14Catalog 12 (⟨547,(2),[12],[2,6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2461 : RecordDataValid section14Catalog 12 (⟨547,(3),[12],[2,6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2462 : RecordDataValid section14Catalog 12 (⟨547,(4),[12],[2,6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2463 : RecordDataValid section14Catalog 12 (⟨547,(5),[12],[2,6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2432).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2432).take 32 = [⟨532,(4),[8,12],[10],3⟩,⟨532,(5),[8,12],[10],3⟩,⟨532,(6),[8,12],[10],3⟩,⟨532,(7),[8,12],[10],3⟩,⟨532,(8),[8,12],[10],3⟩,⟨532,(9),[8,12],[10],3⟩,⟨537,(0),[12],[10],1649⟩,⟨537,(1),[12],[10],1650⟩,⟨537,(2),[12],[10],1651⟩,⟨537,(3),[12],[10],1652⟩,⟨537,(4),[12],[10],17⟩,⟨537,(5),[12],[10],1649⟩,⟨537,(6),[12],[10],1650⟩,⟨537,(7),[12],[10],1651⟩,⟨537,(8),[12],[10],1652⟩,⟨537,(9),[12],[10],17⟩,⟨542,(0),[12],[10],46⟩,⟨542,(1),[12],[10],46⟩,⟨542,(2),[12],[10],42⟩,⟨542,(3),[12],[10],43⟩,⟨542,(4),[12],[10],44⟩,⟨542,(5),[12],[10],47⟩,⟨542,(6),[12],[10],47⟩,⟨542,(7),[12],[10],47⟩,⟨542,(8),[12],[10],43⟩,⟨542,(9),[12],[10],44⟩,⟨547,(0),[12],[2,6],3⟩,⟨547,(1),[12],[2,6],3⟩,⟨547,(2),[12],[2,6],3⟩,⟨547,(3),[12],[2,6],3⟩,⟨547,(4),[12],[2,6],3⟩,⟨547,(5),[12],[2,6],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2432
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2433
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2434
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2435
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2436
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2437
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2438
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2439
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2440
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2441
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2442
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2443
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2444
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2445
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2446
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2447
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2448
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2449
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2450
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2451
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2452
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2453
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2454
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2455
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2456
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2457
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2458
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2459
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2460
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2461
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2462
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2463
end Section14Records_12_2432_2464

#print axioms solution
