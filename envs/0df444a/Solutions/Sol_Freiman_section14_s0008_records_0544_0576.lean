-- Prove2me | solution 1 for Freiman.section14_s0008_records_0544_0576
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:01:40.196783+00:00
-- url     : https://prove2.me/submissions/ad7a5ce0-5ba1-414d-9ba7-f9a42f124a41

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
namespace Section14Records_8_544_576
private theorem valid544 : RecordDataValid section14Catalog 8 (⟨86,(15),[4,8,16],[10],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid545 : RecordDataValid section14Catalog 8 (⟨86,(16),[4,8,16],[10],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid546 : RecordDataValid section14Catalog 8 (⟨86,(17),[4,8,16],[10],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid547 : RecordDataValid section14Catalog 8 (⟨86,(18),[4,8,16],[10],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid548 : RecordDataValid section14Catalog 8 (⟨86,(19),[4,8,16],[10],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid549 : RecordDataValid section14Catalog 8 (⟨86,(20),[4,8,16],[10],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid550 : RecordDataValid section14Catalog 8 (⟨86,(21),[4,8,16],[10],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid551 : RecordDataValid section14Catalog 8 (⟨86,(22),[4,8,16],[10],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid552 : RecordDataValid section14Catalog 8 (⟨86,(23),[4,8,16],[10],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid553 : RecordDataValid section14Catalog 8 (⟨86,(24),[4,8,16],[10],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid554 : RecordDataValid section14Catalog 8 (⟨89,(0),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid555 : RecordDataValid section14Catalog 8 (⟨89,(1),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid556 : RecordDataValid section14Catalog 8 (⟨89,(2),[4,8,12,16],[10],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid557 : RecordDataValid section14Catalog 8 (⟨89,(3),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid558 : RecordDataValid section14Catalog 8 (⟨89,(4),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid559 : RecordDataValid section14Catalog 8 (⟨89,(5),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid560 : RecordDataValid section14Catalog 8 (⟨89,(6),[4,8,12,16],[10],404⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨404,[1,4,5,6,8,9,10,12,13,16],405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid561 : RecordDataValid section14Catalog 8 (⟨89,(7),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid562 : RecordDataValid section14Catalog 8 (⟨89,(8),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid563 : RecordDataValid section14Catalog 8 (⟨89,(9),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid564 : RecordDataValid section14Catalog 8 (⟨89,(10),[4,8,12,16],[10],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid565 : RecordDataValid section14Catalog 8 (⟨89,(11),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid566 : RecordDataValid section14Catalog 8 (⟨89,(12),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid567 : RecordDataValid section14Catalog 8 (⟨89,(13),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid568 : RecordDataValid section14Catalog 8 (⟨89,(14),[4,8,12,16],[10],405⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨405,[1,4,5,6,8,9,10,12,13,16],406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid569 : RecordDataValid section14Catalog 8 (⟨89,(15),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid570 : RecordDataValid section14Catalog 8 (⟨92,(0),[4,8,12,16],[10],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid571 : RecordDataValid section14Catalog 8 (⟨92,(1),[4,8,12,16],[10],407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid572 : RecordDataValid section14Catalog 8 (⟨92,(2),[4,8,12,16],[10],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid573 : RecordDataValid section14Catalog 8 (⟨92,(3),[4,8,12,16],[10],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid574 : RecordDataValid section14Catalog 8 (⟨92,(4),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid575 : RecordDataValid section14Catalog 8 (⟨92,(5),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 544).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 544).take 32 = [⟨86,(15),[4,8,16],[10],21⟩,⟨86,(16),[4,8,16],[10],398⟩,⟨86,(17),[4,8,16],[10],398⟩,⟨86,(18),[4,8,16],[10],398⟩,⟨86,(19),[4,8,16],[10],398⟩,⟨86,(20),[4,8,16],[10],24⟩,⟨86,(21),[4,8,16],[10],399⟩,⟨86,(22),[4,8,16],[10],399⟩,⟨86,(23),[4,8,16],[10],399⟩,⟨86,(24),[4,8,16],[10],399⟩,⟨89,(0),[4,8,12,16],[10],400⟩,⟨89,(1),[4,8,12,16],[10],401⟩,⟨89,(2),[4,8,12,16],[10],402⟩,⟨89,(3),[4,8,12,16],[10],403⟩,⟨89,(4),[4,8,12,16],[10],400⟩,⟨89,(5),[4,8,12,16],[10],401⟩,⟨89,(6),[4,8,12,16],[10],404⟩,⟨89,(7),[4,8,12,16],[10],403⟩,⟨89,(8),[4,8,12,16],[10],400⟩,⟨89,(9),[4,8,12,16],[10],401⟩,⟨89,(10),[4,8,12,16],[10],402⟩,⟨89,(11),[4,8,12,16],[10],403⟩,⟨89,(12),[4,8,12,16],[10],400⟩,⟨89,(13),[4,8,12,16],[10],401⟩,⟨89,(14),[4,8,12,16],[10],405⟩,⟨89,(15),[4,8,12,16],[10],403⟩,⟨92,(0),[4,8,12,16],[10],406⟩,⟨92,(1),[4,8,12,16],[10],407⟩,⟨92,(2),[4,8,12,16],[10],406⟩,⟨92,(3),[4,8,12,16],[10],408⟩,⟨92,(4),[4,8,12,16],[10],409⟩,⟨92,(5),[4,8,12,16],[10],409⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid544
  · exact recordValid_of_data section14Catalog 8 _ hnum valid545
  · exact recordValid_of_data section14Catalog 8 _ hnum valid546
  · exact recordValid_of_data section14Catalog 8 _ hnum valid547
  · exact recordValid_of_data section14Catalog 8 _ hnum valid548
  · exact recordValid_of_data section14Catalog 8 _ hnum valid549
  · exact recordValid_of_data section14Catalog 8 _ hnum valid550
  · exact recordValid_of_data section14Catalog 8 _ hnum valid551
  · exact recordValid_of_data section14Catalog 8 _ hnum valid552
  · exact recordValid_of_data section14Catalog 8 _ hnum valid553
  · exact recordValid_of_data section14Catalog 8 _ hnum valid554
  · exact recordValid_of_data section14Catalog 8 _ hnum valid555
  · exact recordValid_of_data section14Catalog 8 _ hnum valid556
  · exact recordValid_of_data section14Catalog 8 _ hnum valid557
  · exact recordValid_of_data section14Catalog 8 _ hnum valid558
  · exact recordValid_of_data section14Catalog 8 _ hnum valid559
  · exact recordValid_of_data section14Catalog 8 _ hnum valid560
  · exact recordValid_of_data section14Catalog 8 _ hnum valid561
  · exact recordValid_of_data section14Catalog 8 _ hnum valid562
  · exact recordValid_of_data section14Catalog 8 _ hnum valid563
  · exact recordValid_of_data section14Catalog 8 _ hnum valid564
  · exact recordValid_of_data section14Catalog 8 _ hnum valid565
  · exact recordValid_of_data section14Catalog 8 _ hnum valid566
  · exact recordValid_of_data section14Catalog 8 _ hnum valid567
  · exact recordValid_of_data section14Catalog 8 _ hnum valid568
  · exact recordValid_of_data section14Catalog 8 _ hnum valid569
  · exact recordValid_of_data section14Catalog 8 _ hnum valid570
  · exact recordValid_of_data section14Catalog 8 _ hnum valid571
  · exact recordValid_of_data section14Catalog 8 _ hnum valid572
  · exact recordValid_of_data section14Catalog 8 _ hnum valid573
  · exact recordValid_of_data section14Catalog 8 _ hnum valid574
  · exact recordValid_of_data section14Catalog 8 _ hnum valid575
end Section14Records_8_544_576

#print axioms solution
