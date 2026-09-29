-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_2496_2624
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:26:02.047837+00:00
-- url     : https://prove2.me/submissions/6293915a-85c5-44f3-8ff8-e544e4aee6e8

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2496_2528
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2496_2528
private theorem valid2496 : RecordDataValid section14Catalog 5 (⟨153,(-1),[1,3,5,7,9,11,13,15],[0],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2497 : RecordDataValid section14Catalog 5 (⟨153,(-1),[1,5,6,13],[194,198],880⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2498 : RecordDataValid section14Catalog 5 (⟨153,(-1),[1,5,9,13],[4],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2499 : RecordDataValid section14Catalog 5 (⟨153,(-1),[1,5,13],[16,20,40,44,56,60],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2500 : RecordDataValid section14Catalog 5 (⟨153,(-1),[1,5,13],[195,199,211,215,235,239,251,255],880⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2501 : RecordDataValid section14Catalog 5 (⟨153,(-1),[5,6],[131,135],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2502 : RecordDataValid section14Catalog 5 (⟨155,(0),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2503 : RecordDataValid section14Catalog 5 (⟨155,(0),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2504 : RecordDataValid section14Catalog 5 (⟨155,(1),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2505 : RecordDataValid section14Catalog 5 (⟨155,(1),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2506 : RecordDataValid section14Catalog 5 (⟨155,(2),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2507 : RecordDataValid section14Catalog 5 (⟨155,(2),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2508 : RecordDataValid section14Catalog 5 (⟨155,(3),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2509 : RecordDataValid section14Catalog 5 (⟨155,(3),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2510 : RecordDataValid section14Catalog 5 (⟨155,(4),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2511 : RecordDataValid section14Catalog 5 (⟨155,(4),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2512 : RecordDataValid section14Catalog 5 (⟨155,(5),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2513 : RecordDataValid section14Catalog 5 (⟨155,(5),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2514 : RecordDataValid section14Catalog 5 (⟨155,(6),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2515 : RecordDataValid section14Catalog 5 (⟨155,(6),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2516 : RecordDataValid section14Catalog 5 (⟨155,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2517 : RecordDataValid section14Catalog 5 (⟨155,(7),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2518 : RecordDataValid section14Catalog 5 (⟨155,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2519 : RecordDataValid section14Catalog 5 (⟨155,(8),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2520 : RecordDataValid section14Catalog 5 (⟨155,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2521 : RecordDataValid section14Catalog 5 (⟨155,(9),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2522 : RecordDataValid section14Catalog 5 (⟨155,(10),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2523 : RecordDataValid section14Catalog 5 (⟨155,(10),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2524 : RecordDataValid section14Catalog 5 (⟨155,(11),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2525 : RecordDataValid section14Catalog 5 (⟨155,(11),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2526 : RecordDataValid section14Catalog 5 (⟨155,(12),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2527 : RecordDataValid section14Catalog 5 (⟨155,(12),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2496_2528 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2496).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2496).take 32 = [⟨153,(-1),[1,3,5,7,9,11,13,15],[0],631⟩,⟨153,(-1),[1,5,6,13],[194,198],880⟩,⟨153,(-1),[1,5,9,13],[4],631⟩,⟨153,(-1),[1,5,13],[16,20,40,44,56,60],631⟩,⟨153,(-1),[1,5,13],[195,199,211,215,235,239,251,255],880⟩,⟨153,(-1),[5,6],[131,135],636⟩,⟨155,(0),[1,2,5,6,13,14],[170],3⟩,⟨155,(0),[5,6],[174],3⟩,⟨155,(1),[1,2,5,6,13,14],[170],3⟩,⟨155,(1),[5,6],[174],3⟩,⟨155,(2),[1,2,5,6,13,14],[170],3⟩,⟨155,(2),[5,6],[174],3⟩,⟨155,(3),[1,2,5,6,13,14],[170],3⟩,⟨155,(3),[5,6],[174],3⟩,⟨155,(4),[1,2,5,6,13,14],[170],3⟩,⟨155,(4),[5,6],[174],3⟩,⟨155,(5),[1,2,5,6,13,14],[170],3⟩,⟨155,(5),[5,6],[174],3⟩,⟨155,(6),[1,2,5,6,13,14],[170],3⟩,⟨155,(6),[5,6],[174],3⟩,⟨155,(7),[1,2,5,6,13,14],[170],3⟩,⟨155,(7),[5,6],[174],3⟩,⟨155,(8),[1,2,5,6,13,14],[170],3⟩,⟨155,(8),[5,6],[174],3⟩,⟨155,(9),[1,2,5,6,13,14],[170],3⟩,⟨155,(9),[5,6],[174],3⟩,⟨155,(10),[1,2,5,6,13,14],[170],3⟩,⟨155,(10),[5,6],[174],3⟩,⟨155,(11),[1,2,5,6,13,14],[170],3⟩,⟨155,(11),[5,6],[174],3⟩,⟨155,(12),[1,2,5,6,13,14],[170],3⟩,⟨155,(12),[5,6],[174],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2496
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2497
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2498
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2499
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2500
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2501
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2502
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2503
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2504
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2505
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2506
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2507
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2508
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2509
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2510
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2511
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2512
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2513
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2514
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2515
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2516
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2517
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2518
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2519
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2520
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2521
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2522
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2523
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2524
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2525
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2526
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2527
end Section14Records_5_2496_2528

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2496_2528


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2528_2560
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2528_2560
private theorem valid2528 : RecordDataValid section14Catalog 5 (⟨155,(13),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2529 : RecordDataValid section14Catalog 5 (⟨155,(13),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2530 : RecordDataValid section14Catalog 5 (⟨155,(14),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2531 : RecordDataValid section14Catalog 5 (⟨155,(14),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2532 : RecordDataValid section14Catalog 5 (⟨155,(15),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2533 : RecordDataValid section14Catalog 5 (⟨155,(15),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2534 : RecordDataValid section14Catalog 5 (⟨155,(16),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2535 : RecordDataValid section14Catalog 5 (⟨155,(16),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2536 : RecordDataValid section14Catalog 5 (⟨155,(17),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2537 : RecordDataValid section14Catalog 5 (⟨155,(17),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2538 : RecordDataValid section14Catalog 5 (⟨155,(18),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2539 : RecordDataValid section14Catalog 5 (⟨155,(18),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2540 : RecordDataValid section14Catalog 5 (⟨155,(19),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2541 : RecordDataValid section14Catalog 5 (⟨155,(19),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2542 : RecordDataValid section14Catalog 5 (⟨155,(20),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2543 : RecordDataValid section14Catalog 5 (⟨155,(20),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2544 : RecordDataValid section14Catalog 5 (⟨155,(21),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2545 : RecordDataValid section14Catalog 5 (⟨155,(21),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2546 : RecordDataValid section14Catalog 5 (⟨155,(22),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2547 : RecordDataValid section14Catalog 5 (⟨155,(22),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2548 : RecordDataValid section14Catalog 5 (⟨155,(23),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2549 : RecordDataValid section14Catalog 5 (⟨155,(23),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2550 : RecordDataValid section14Catalog 5 (⟨155,(24),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2551 : RecordDataValid section14Catalog 5 (⟨155,(24),[5,6],[174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2552 : RecordDataValid section14Catalog 5 (⟨157,(0),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2553 : RecordDataValid section14Catalog 5 (⟨157,(0),[5,6],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2554 : RecordDataValid section14Catalog 5 (⟨157,(1),[1,2,5,6,13,14],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2555 : RecordDataValid section14Catalog 5 (⟨157,(1),[5,6],[174],289⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨289,[1,2,3,5,6,7,13,14,15],290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2556 : RecordDataValid section14Catalog 5 (⟨157,(2),[1,2,5,6,13,14],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2557 : RecordDataValid section14Catalog 5 (⟨157,(2),[5,6],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2558 : RecordDataValid section14Catalog 5 (⟨157,(3),[1,2,5,6,13,14],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2559 : RecordDataValid section14Catalog 5 (⟨157,(3),[5,6],[174],290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨290,[1,2,3,5,6,7,13,14,15],291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2528_2560 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2528).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2528).take 32 = [⟨155,(13),[1,2,5,6,13,14],[170],3⟩,⟨155,(13),[5,6],[174],3⟩,⟨155,(14),[1,2,5,6,13,14],[170],3⟩,⟨155,(14),[5,6],[174],3⟩,⟨155,(15),[1,2,5,6,13,14],[170],3⟩,⟨155,(15),[5,6],[174],3⟩,⟨155,(16),[1,2,5,6,13,14],[170],3⟩,⟨155,(16),[5,6],[174],3⟩,⟨155,(17),[1,2,5,6,13,14],[170],3⟩,⟨155,(17),[5,6],[174],3⟩,⟨155,(18),[1,2,5,6,13,14],[170],3⟩,⟨155,(18),[5,6],[174],3⟩,⟨155,(19),[1,2,5,6,13,14],[170],3⟩,⟨155,(19),[5,6],[174],3⟩,⟨155,(20),[1,2,5,6,13,14],[170],3⟩,⟨155,(20),[5,6],[174],3⟩,⟨155,(21),[1,2,5,6,13,14],[170],3⟩,⟨155,(21),[5,6],[174],3⟩,⟨155,(22),[1,2,5,6,13,14],[170],3⟩,⟨155,(22),[5,6],[174],3⟩,⟨155,(23),[1,2,5,6,13,14],[170],3⟩,⟨155,(23),[5,6],[174],3⟩,⟨155,(24),[1,2,5,6,13,14],[170],3⟩,⟨155,(24),[5,6],[174],3⟩,⟨157,(0),[1,2,5,6,13,14],[170],10⟩,⟨157,(0),[5,6],[174],288⟩,⟨157,(1),[1,2,5,6,13,14],[170],393⟩,⟨157,(1),[5,6],[174],289⟩,⟨157,(2),[1,2,5,6,13,14],[170],394⟩,⟨157,(2),[5,6],[174],288⟩,⟨157,(3),[1,2,5,6,13,14],[170],395⟩,⟨157,(3),[5,6],[174],290⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2528
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2529
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2530
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2531
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2532
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2533
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2534
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2535
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2536
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2537
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2538
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2539
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2540
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2541
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2542
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2543
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2544
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2545
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2546
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2547
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2548
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2549
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2550
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2551
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2552
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2553
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2554
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2555
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2556
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2557
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2558
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2559
end Section14Records_5_2528_2560

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2528_2560


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2560_2592
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2560_2592
private theorem valid2560 : RecordDataValid section14Catalog 5 (⟨157,(4),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2561 : RecordDataValid section14Catalog 5 (⟨157,(4),[5,6],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2562 : RecordDataValid section14Catalog 5 (⟨157,(5),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2563 : RecordDataValid section14Catalog 5 (⟨157,(5),[5,6],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2564 : RecordDataValid section14Catalog 5 (⟨157,(6),[1,2,5,6,13,14],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2565 : RecordDataValid section14Catalog 5 (⟨157,(6),[5,6],[174],289⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨289,[1,2,3,5,6,7,13,14,15],290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2566 : RecordDataValid section14Catalog 5 (⟨157,(7),[1,2,5,6,13,14],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2567 : RecordDataValid section14Catalog 5 (⟨157,(7),[5,6],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2568 : RecordDataValid section14Catalog 5 (⟨157,(8),[1,2,5,6,13,14],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2569 : RecordDataValid section14Catalog 5 (⟨157,(8),[5,6],[174],290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨290,[1,2,3,5,6,7,13,14,15],291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2570 : RecordDataValid section14Catalog 5 (⟨157,(9),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2571 : RecordDataValid section14Catalog 5 (⟨157,(9),[5,6],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2572 : RecordDataValid section14Catalog 5 (⟨157,(10),[1,2,5,6,13,14],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2573 : RecordDataValid section14Catalog 5 (⟨157,(10),[5,6],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2574 : RecordDataValid section14Catalog 5 (⟨157,(11),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2575 : RecordDataValid section14Catalog 5 (⟨157,(11),[5,6],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2576 : RecordDataValid section14Catalog 5 (⟨157,(12),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2577 : RecordDataValid section14Catalog 5 (⟨157,(12),[5,6],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2578 : RecordDataValid section14Catalog 5 (⟨157,(13),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2579 : RecordDataValid section14Catalog 5 (⟨157,(13),[5,6],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2580 : RecordDataValid section14Catalog 5 (⟨157,(14),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2581 : RecordDataValid section14Catalog 5 (⟨157,(14),[5,6],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2582 : RecordDataValid section14Catalog 5 (⟨157,(15),[1,2,5,6,13,14],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2583 : RecordDataValid section14Catalog 5 (⟨157,(15),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2584 : RecordDataValid section14Catalog 5 (⟨157,(16),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2585 : RecordDataValid section14Catalog 5 (⟨157,(16),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2586 : RecordDataValid section14Catalog 5 (⟨157,(17),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2587 : RecordDataValid section14Catalog 5 (⟨157,(17),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2588 : RecordDataValid section14Catalog 5 (⟨157,(18),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2589 : RecordDataValid section14Catalog 5 (⟨157,(18),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2590 : RecordDataValid section14Catalog 5 (⟨157,(19),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2591 : RecordDataValid section14Catalog 5 (⟨157,(19),[5,6],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2560_2592 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2560).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2560).take 32 = [⟨157,(4),[1,2,5,6,13,14],[170],396⟩,⟨157,(4),[5,6],[174],291⟩,⟨157,(5),[1,2,5,6,13,14],[170],10⟩,⟨157,(5),[5,6],[174],288⟩,⟨157,(6),[1,2,5,6,13,14],[170],393⟩,⟨157,(6),[5,6],[174],289⟩,⟨157,(7),[1,2,5,6,13,14],[170],394⟩,⟨157,(7),[5,6],[174],288⟩,⟨157,(8),[1,2,5,6,13,14],[170],395⟩,⟨157,(8),[5,6],[174],290⟩,⟨157,(9),[1,2,5,6,13,14],[170],396⟩,⟨157,(9),[5,6],[174],291⟩,⟨157,(10),[1,2,5,6,13,14],[170],18⟩,⟨157,(10),[5,6],[174],292⟩,⟨157,(11),[1,2,5,6,13,14],[170],397⟩,⟨157,(11),[5,6],[174],292⟩,⟨157,(12),[1,2,5,6,13,14],[170],397⟩,⟨157,(12),[5,6],[174],292⟩,⟨157,(13),[1,2,5,6,13,14],[170],397⟩,⟨157,(13),[5,6],[174],292⟩,⟨157,(14),[1,2,5,6,13,14],[170],396⟩,⟨157,(14),[5,6],[174],291⟩,⟨157,(15),[1,2,5,6,13,14],[170],21⟩,⟨157,(15),[5,6],[174],293⟩,⟨157,(16),[1,2,5,6,13,14],[170],398⟩,⟨157,(16),[5,6],[174],293⟩,⟨157,(17),[1,2,5,6,13,14],[170],398⟩,⟨157,(17),[5,6],[174],293⟩,⟨157,(18),[1,2,5,6,13,14],[170],398⟩,⟨157,(18),[5,6],[174],293⟩,⟨157,(19),[1,2,5,6,13,14],[170],398⟩,⟨157,(19),[5,6],[174],293⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2560
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2561
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2562
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2563
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2564
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2565
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2566
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2567
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2568
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2569
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2570
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2571
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2572
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2573
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2574
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2575
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2576
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2577
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2578
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2579
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2580
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2581
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2582
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2583
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2584
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2585
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2586
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2587
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2588
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2589
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2590
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2591
end Section14Records_5_2560_2592

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2560_2592


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2592_2624
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2592_2624
private theorem valid2592 : RecordDataValid section14Catalog 5 (⟨157,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2593 : RecordDataValid section14Catalog 5 (⟨157,(20),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2594 : RecordDataValid section14Catalog 5 (⟨157,(21),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2595 : RecordDataValid section14Catalog 5 (⟨157,(21),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2596 : RecordDataValid section14Catalog 5 (⟨157,(22),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2597 : RecordDataValid section14Catalog 5 (⟨157,(22),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2598 : RecordDataValid section14Catalog 5 (⟨157,(23),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2599 : RecordDataValid section14Catalog 5 (⟨157,(23),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2600 : RecordDataValid section14Catalog 5 (⟨157,(24),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2601 : RecordDataValid section14Catalog 5 (⟨157,(24),[5,6],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2602 : RecordDataValid section14Catalog 5 (⟨160,(0),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2603 : RecordDataValid section14Catalog 5 (⟨160,(0),[5,6],[174],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2604 : RecordDataValid section14Catalog 5 (⟨160,(1),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2605 : RecordDataValid section14Catalog 5 (⟨160,(1),[5,6],[174],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2606 : RecordDataValid section14Catalog 5 (⟨160,(2),[1,2,5,6,13,14],[170],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2607 : RecordDataValid section14Catalog 5 (⟨160,(2),[5,6],[174],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2608 : RecordDataValid section14Catalog 5 (⟨160,(3),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2609 : RecordDataValid section14Catalog 5 (⟨160,(3),[5,6],[174],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2610 : RecordDataValid section14Catalog 5 (⟨160,(4),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2611 : RecordDataValid section14Catalog 5 (⟨160,(4),[5,6],[174],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2612 : RecordDataValid section14Catalog 5 (⟨160,(5),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2613 : RecordDataValid section14Catalog 5 (⟨160,(5),[5,6],[174],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2614 : RecordDataValid section14Catalog 5 (⟨160,(6),[1,2,5,6,13,14],[170],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2615 : RecordDataValid section14Catalog 5 (⟨160,(6),[5,6],[174],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2616 : RecordDataValid section14Catalog 5 (⟨160,(7),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2617 : RecordDataValid section14Catalog 5 (⟨160,(7),[5,6],[174],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2618 : RecordDataValid section14Catalog 5 (⟨160,(8),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2619 : RecordDataValid section14Catalog 5 (⟨160,(8),[5,6],[174],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2620 : RecordDataValid section14Catalog 5 (⟨160,(9),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2621 : RecordDataValid section14Catalog 5 (⟨160,(9),[5,6],[174],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2622 : RecordDataValid section14Catalog 5 (⟨160,(10),[1,2,5,6,13,14],[170],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2623 : RecordDataValid section14Catalog 5 (⟨160,(10),[5,6],[174],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2592_2624 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2592).take 32 = [⟨157,(20),[1,2,5,6,13,14],[170],24⟩,⟨157,(20),[5,6],[174],294⟩,⟨157,(21),[1,2,5,6,13,14],[170],399⟩,⟨157,(21),[5,6],[174],294⟩,⟨157,(22),[1,2,5,6,13,14],[170],399⟩,⟨157,(22),[5,6],[174],294⟩,⟨157,(23),[1,2,5,6,13,14],[170],399⟩,⟨157,(23),[5,6],[174],294⟩,⟨157,(24),[1,2,5,6,13,14],[170],399⟩,⟨157,(24),[5,6],[174],294⟩,⟨160,(0),[1,2,5,6,13,14],[170],638⟩,⟨160,(0),[5,6],[174],638⟩,⟨160,(1),[1,2,5,6,13,14],[170],639⟩,⟨160,(1),[5,6],[174],639⟩,⟨160,(2),[1,2,5,6,13,14],[170],640⟩,⟨160,(2),[5,6],[174],640⟩,⟨160,(3),[1,2,5,6,13,14],[170],641⟩,⟨160,(3),[5,6],[174],641⟩,⟨160,(4),[1,2,5,6,13,14],[170],638⟩,⟨160,(4),[5,6],[174],638⟩,⟨160,(5),[1,2,5,6,13,14],[170],639⟩,⟨160,(5),[5,6],[174],639⟩,⟨160,(6),[1,2,5,6,13,14],[170],642⟩,⟨160,(6),[5,6],[174],642⟩,⟨160,(7),[1,2,5,6,13,14],[170],641⟩,⟨160,(7),[5,6],[174],641⟩,⟨160,(8),[1,2,5,6,13,14],[170],638⟩,⟨160,(8),[5,6],[174],638⟩,⟨160,(9),[1,2,5,6,13,14],[170],639⟩,⟨160,(9),[5,6],[174],639⟩,⟨160,(10),[1,2,5,6,13,14],[170],640⟩,⟨160,(10),[5,6],[174],640⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2592
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2593
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2594
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2595
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2596
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2597
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2598
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2599
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2600
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2601
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2602
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2603
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2604
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2605
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2606
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2607
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2608
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2609
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2610
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2611
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2612
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2613
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2614
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2615
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2616
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2617
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2618
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2619
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2620
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2621
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2622
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2623
end Section14Records_5_2592_2624

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2592_2624

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2496).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 2496 2560 2624 (by decide) (by decide) (all_of_interval_split P xs 2496 2528 2560 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_2496_2528 hnum) (Freiman.workReverse20260919_s0005_records_2528_2560 hnum)) (all_of_interval_split P xs 2560 2592 2624 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_2560_2592 hnum) (Freiman.workReverse20260919_s0005_records_2592_2624 hnum)))

#print axioms solution
