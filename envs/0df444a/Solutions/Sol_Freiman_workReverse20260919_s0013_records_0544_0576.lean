-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_0544_0576
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:14:23.357894+00:00
-- url     : https://prove2.me/submissions/46870217-5307-45ff-bde3-dc7c2a01965b

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
namespace Section14Records_13_544_576
private theorem valid544 : RecordDataValid section14Catalog 13 (⟨23,(22),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid545 : RecordDataValid section14Catalog 13 (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid546 : RecordDataValid section14Catalog 13 (⟨23,(23),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid547 : RecordDataValid section14Catalog 13 (⟨23,(23),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid548 : RecordDataValid section14Catalog 13 (⟨23,(23),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid549 : RecordDataValid section14Catalog 13 (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid550 : RecordDataValid section14Catalog 13 (⟨23,(24),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid551 : RecordDataValid section14Catalog 13 (⟨23,(24),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid552 : RecordDataValid section14Catalog 13 (⟨23,(24),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid553 : RecordDataValid section14Catalog 13 (⟨25,(0),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid554 : RecordDataValid section14Catalog 13 (⟨25,(0),[1,2,5,6,13,14],[150],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid555 : RecordDataValid section14Catalog 13 (⟨25,(0),[1,2,13,14],[131],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid556 : RecordDataValid section14Catalog 13 (⟨25,(0),[1,2,13,14],[147],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid557 : RecordDataValid section14Catalog 13 (⟨25,(0),[1,2,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid558 : RecordDataValid section14Catalog 13 (⟨25,(0),[1,13],[135],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid559 : RecordDataValid section14Catalog 13 (⟨25,(0),[1,13],[151],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid560 : RecordDataValid section14Catalog 13 (⟨25,(1),[1,2,5,6,13,14],[146],146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨146,[1,2,3,5,6,7,13,14,15],146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid561 : RecordDataValid section14Catalog 13 (⟨25,(1),[1,2,13,14],[131],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid562 : RecordDataValid section14Catalog 13 (⟨25,(1),[1,2,13,14],[147],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid563 : RecordDataValid section14Catalog 13 (⟨25,(1),[1,2,13,14],[150],190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨190,[1,2,3,4,5,6,7,13,14,15,16],190⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid564 : RecordDataValid section14Catalog 13 (⟨25,(1),[1,2,13,14],[190],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid565 : RecordDataValid section14Catalog 13 (⟨25,(1),[1,13],[135],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid566 : RecordDataValid section14Catalog 13 (⟨25,(1),[1,13],[151],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid567 : RecordDataValid section14Catalog 13 (⟨25,(2),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid568 : RecordDataValid section14Catalog 13 (⟨25,(2),[1,2,13,14],[131],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid569 : RecordDataValid section14Catalog 13 (⟨25,(2),[1,2,13,14],[147],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid570 : RecordDataValid section14Catalog 13 (⟨25,(2),[1,2,13,14],[150],191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨191,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],191⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid571 : RecordDataValid section14Catalog 13 (⟨25,(2),[1,2,13,14],[190],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid572 : RecordDataValid section14Catalog 13 (⟨25,(2),[1,13],[135],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid573 : RecordDataValid section14Catalog 13 (⟨25,(2),[1,13],[151],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid574 : RecordDataValid section14Catalog 13 (⟨25,(3),[1,2,5,6,13,14],[146],147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨147,[1,2,3,5,6,7,13,14,15],147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid575 : RecordDataValid section14Catalog 13 (⟨25,(3),[1,2,13,14],[131],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 544).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 544).take 32 = [⟨23,(22),[1,13],[151],2⟩,⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(23),[1,2,13,14],[147,190],2⟩,⟨23,(23),[1,5,13],[135],2⟩,⟨23,(23),[1,13],[151],2⟩,⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(24),[1,2,13,14],[147,190],2⟩,⟨23,(24),[1,5,13],[135],2⟩,⟨23,(24),[1,13],[151],2⟩,⟨25,(0),[1,2,5,6,13,14],[146],145⟩,⟨25,(0),[1,2,5,6,13,14],[150],189⟩,⟨25,(0),[1,2,13,14],[131],80⟩,⟨25,(0),[1,2,13,14],[147],167⟩,⟨25,(0),[1,2,13,14],[190],189⟩,⟨25,(0),[1,13],[135],80⟩,⟨25,(0),[1,13],[151],167⟩,⟨25,(1),[1,2,5,6,13,14],[146],146⟩,⟨25,(1),[1,2,13,14],[131],81⟩,⟨25,(1),[1,2,13,14],[147],168⟩,⟨25,(1),[1,2,13,14],[150],190⟩,⟨25,(1),[1,2,13,14],[190],216⟩,⟨25,(1),[1,13],[135],81⟩,⟨25,(1),[1,13],[151],168⟩,⟨25,(2),[1,2,5,6,13,14],[146],145⟩,⟨25,(2),[1,2,13,14],[131],80⟩,⟨25,(2),[1,2,13,14],[147],167⟩,⟨25,(2),[1,2,13,14],[150],191⟩,⟨25,(2),[1,2,13,14],[190],217⟩,⟨25,(2),[1,13],[135],80⟩,⟨25,(2),[1,13],[151],167⟩,⟨25,(3),[1,2,5,6,13,14],[146],147⟩,⟨25,(3),[1,2,13,14],[131],82⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid544
  · exact recordValid_of_data section14Catalog 13 _ hnum valid545
  · exact recordValid_of_data section14Catalog 13 _ hnum valid546
  · exact recordValid_of_data section14Catalog 13 _ hnum valid547
  · exact recordValid_of_data section14Catalog 13 _ hnum valid548
  · exact recordValid_of_data section14Catalog 13 _ hnum valid549
  · exact recordValid_of_data section14Catalog 13 _ hnum valid550
  · exact recordValid_of_data section14Catalog 13 _ hnum valid551
  · exact recordValid_of_data section14Catalog 13 _ hnum valid552
  · exact recordValid_of_data section14Catalog 13 _ hnum valid553
  · exact recordValid_of_data section14Catalog 13 _ hnum valid554
  · exact recordValid_of_data section14Catalog 13 _ hnum valid555
  · exact recordValid_of_data section14Catalog 13 _ hnum valid556
  · exact recordValid_of_data section14Catalog 13 _ hnum valid557
  · exact recordValid_of_data section14Catalog 13 _ hnum valid558
  · exact recordValid_of_data section14Catalog 13 _ hnum valid559
  · exact recordValid_of_data section14Catalog 13 _ hnum valid560
  · exact recordValid_of_data section14Catalog 13 _ hnum valid561
  · exact recordValid_of_data section14Catalog 13 _ hnum valid562
  · exact recordValid_of_data section14Catalog 13 _ hnum valid563
  · exact recordValid_of_data section14Catalog 13 _ hnum valid564
  · exact recordValid_of_data section14Catalog 13 _ hnum valid565
  · exact recordValid_of_data section14Catalog 13 _ hnum valid566
  · exact recordValid_of_data section14Catalog 13 _ hnum valid567
  · exact recordValid_of_data section14Catalog 13 _ hnum valid568
  · exact recordValid_of_data section14Catalog 13 _ hnum valid569
  · exact recordValid_of_data section14Catalog 13 _ hnum valid570
  · exact recordValid_of_data section14Catalog 13 _ hnum valid571
  · exact recordValid_of_data section14Catalog 13 _ hnum valid572
  · exact recordValid_of_data section14Catalog 13 _ hnum valid573
  · exact recordValid_of_data section14Catalog 13 _ hnum valid574
  · exact recordValid_of_data section14Catalog 13 _ hnum valid575
end Section14Records_13_544_576

#print axioms solution
