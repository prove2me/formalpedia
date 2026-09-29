-- Prove2me | solution 1 for Freiman.section14_s0004_records_0608_0640
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:14:45.642177+00:00
-- url     : https://prove2.me/submissions/36772fdd-c8cf-48e1-8836-dc095dbae96b

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
namespace Section14Records_4_608_640
private theorem valid608 : RecordDataValid section14Catalog 4 (⟨86,(20),[4,8,16],[10],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid609 : RecordDataValid section14Catalog 4 (⟨86,(21),[4,8,16],[10],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid610 : RecordDataValid section14Catalog 4 (⟨86,(22),[4,8,16],[10],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid611 : RecordDataValid section14Catalog 4 (⟨86,(23),[4,8,16],[10],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid612 : RecordDataValid section14Catalog 4 (⟨86,(24),[4,8,16],[10],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid613 : RecordDataValid section14Catalog 4 (⟨89,(0),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid614 : RecordDataValid section14Catalog 4 (⟨89,(1),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid615 : RecordDataValid section14Catalog 4 (⟨89,(2),[4,8,12,16],[10],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid616 : RecordDataValid section14Catalog 4 (⟨89,(3),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid617 : RecordDataValid section14Catalog 4 (⟨89,(4),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid618 : RecordDataValid section14Catalog 4 (⟨89,(5),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid619 : RecordDataValid section14Catalog 4 (⟨89,(6),[4,8,12,16],[10],404⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨404,[1,4,5,6,8,9,10,12,13,16],405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid620 : RecordDataValid section14Catalog 4 (⟨89,(7),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid621 : RecordDataValid section14Catalog 4 (⟨89,(8),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid622 : RecordDataValid section14Catalog 4 (⟨89,(9),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid623 : RecordDataValid section14Catalog 4 (⟨89,(10),[4,8,12,16],[10],402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid624 : RecordDataValid section14Catalog 4 (⟨89,(11),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid625 : RecordDataValid section14Catalog 4 (⟨89,(12),[4,8,12,16],[10],400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid626 : RecordDataValid section14Catalog 4 (⟨89,(13),[4,8,12,16],[10],401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid627 : RecordDataValid section14Catalog 4 (⟨89,(14),[4,8,12,16],[10],405⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨405,[1,4,5,6,8,9,10,12,13,16],406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid628 : RecordDataValid section14Catalog 4 (⟨89,(15),[4,8,12,16],[10],403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid629 : RecordDataValid section14Catalog 4 (⟨92,(0),[4,8,12,16],[10],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid630 : RecordDataValid section14Catalog 4 (⟨92,(1),[4,8,12,16],[10],407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid631 : RecordDataValid section14Catalog 4 (⟨92,(2),[4,8,12,16],[10],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid632 : RecordDataValid section14Catalog 4 (⟨92,(3),[4,8,12,16],[10],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid633 : RecordDataValid section14Catalog 4 (⟨92,(4),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid634 : RecordDataValid section14Catalog 4 (⟨92,(5),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid635 : RecordDataValid section14Catalog 4 (⟨92,(6),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid636 : RecordDataValid section14Catalog 4 (⟨92,(7),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid637 : RecordDataValid section14Catalog 4 (⟨92,(8),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid638 : RecordDataValid section14Catalog 4 (⟨92,(9),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid639 : RecordDataValid section14Catalog 4 (⟨92,(10),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 608).take 32 = [⟨86,(20),[4,8,16],[10],24⟩,⟨86,(21),[4,8,16],[10],399⟩,⟨86,(22),[4,8,16],[10],399⟩,⟨86,(23),[4,8,16],[10],399⟩,⟨86,(24),[4,8,16],[10],399⟩,⟨89,(0),[4,8,12,16],[10],400⟩,⟨89,(1),[4,8,12,16],[10],401⟩,⟨89,(2),[4,8,12,16],[10],402⟩,⟨89,(3),[4,8,12,16],[10],403⟩,⟨89,(4),[4,8,12,16],[10],400⟩,⟨89,(5),[4,8,12,16],[10],401⟩,⟨89,(6),[4,8,12,16],[10],404⟩,⟨89,(7),[4,8,12,16],[10],403⟩,⟨89,(8),[4,8,12,16],[10],400⟩,⟨89,(9),[4,8,12,16],[10],401⟩,⟨89,(10),[4,8,12,16],[10],402⟩,⟨89,(11),[4,8,12,16],[10],403⟩,⟨89,(12),[4,8,12,16],[10],400⟩,⟨89,(13),[4,8,12,16],[10],401⟩,⟨89,(14),[4,8,12,16],[10],405⟩,⟨89,(15),[4,8,12,16],[10],403⟩,⟨92,(0),[4,8,12,16],[10],406⟩,⟨92,(1),[4,8,12,16],[10],407⟩,⟨92,(2),[4,8,12,16],[10],406⟩,⟨92,(3),[4,8,12,16],[10],408⟩,⟨92,(4),[4,8,12,16],[10],409⟩,⟨92,(5),[4,8,12,16],[10],409⟩,⟨92,(6),[4,8,12,16],[10],409⟩,⟨92,(7),[4,8,12,16],[10],409⟩,⟨92,(8),[4,8,12,16],[10],410⟩,⟨92,(9),[4,8,12,16],[10],410⟩,⟨92,(10),[4,8,12,16],[10],410⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid608
  · exact recordValid_of_data section14Catalog 4 _ hnum valid609
  · exact recordValid_of_data section14Catalog 4 _ hnum valid610
  · exact recordValid_of_data section14Catalog 4 _ hnum valid611
  · exact recordValid_of_data section14Catalog 4 _ hnum valid612
  · exact recordValid_of_data section14Catalog 4 _ hnum valid613
  · exact recordValid_of_data section14Catalog 4 _ hnum valid614
  · exact recordValid_of_data section14Catalog 4 _ hnum valid615
  · exact recordValid_of_data section14Catalog 4 _ hnum valid616
  · exact recordValid_of_data section14Catalog 4 _ hnum valid617
  · exact recordValid_of_data section14Catalog 4 _ hnum valid618
  · exact recordValid_of_data section14Catalog 4 _ hnum valid619
  · exact recordValid_of_data section14Catalog 4 _ hnum valid620
  · exact recordValid_of_data section14Catalog 4 _ hnum valid621
  · exact recordValid_of_data section14Catalog 4 _ hnum valid622
  · exact recordValid_of_data section14Catalog 4 _ hnum valid623
  · exact recordValid_of_data section14Catalog 4 _ hnum valid624
  · exact recordValid_of_data section14Catalog 4 _ hnum valid625
  · exact recordValid_of_data section14Catalog 4 _ hnum valid626
  · exact recordValid_of_data section14Catalog 4 _ hnum valid627
  · exact recordValid_of_data section14Catalog 4 _ hnum valid628
  · exact recordValid_of_data section14Catalog 4 _ hnum valid629
  · exact recordValid_of_data section14Catalog 4 _ hnum valid630
  · exact recordValid_of_data section14Catalog 4 _ hnum valid631
  · exact recordValid_of_data section14Catalog 4 _ hnum valid632
  · exact recordValid_of_data section14Catalog 4 _ hnum valid633
  · exact recordValid_of_data section14Catalog 4 _ hnum valid634
  · exact recordValid_of_data section14Catalog 4 _ hnum valid635
  · exact recordValid_of_data section14Catalog 4 _ hnum valid636
  · exact recordValid_of_data section14Catalog 4 _ hnum valid637
  · exact recordValid_of_data section14Catalog 4 _ hnum valid638
  · exact recordValid_of_data section14Catalog 4 _ hnum valid639
end Section14Records_4_608_640

#print axioms solution
