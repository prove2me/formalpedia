-- Prove2me | solution 1 for Freiman.section14_s0016_records_0608_0640
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T22:56:46.923071+00:00
-- url     : https://prove2.me/submissions/f780cb5a-b3dc-4d63-a111-6e30468a1bfa

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
namespace Section14Records_16_608_640
private theorem valid608 : RecordDataValid section14Catalog 16 (⟨119,(4),[4,8,12,16],[10],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid609 : RecordDataValid section14Catalog 16 (⟨119,(5),[4,8,12,16],[10],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid610 : RecordDataValid section14Catalog 16 (⟨119,(6),[4,8,12,16],[10],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid611 : RecordDataValid section14Catalog 16 (⟨119,(7),[4,8,12,16],[10],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid612 : RecordDataValid section14Catalog 16 (⟨119,(8),[4,8,12,16],[10],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid613 : RecordDataValid section14Catalog 16 (⟨119,(9),[4,8,12,16],[10],475⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid614 : RecordDataValid section14Catalog 16 (⟨119,(10),[4,8,12,16],[10],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid615 : RecordDataValid section14Catalog 16 (⟨119,(11),[4,8,12,16],[10],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid616 : RecordDataValid section14Catalog 16 (⟨119,(12),[4,8,12,16],[10],478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨478,[1,4,5,6,8,9,10,12,13,16],479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid617 : RecordDataValid section14Catalog 16 (⟨119,(13),[4,8,12,16],[10],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid618 : RecordDataValid section14Catalog 16 (⟨119,(14),[4,8,12,16],[10],479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨479,[1,4,5,6,8,9,10,12,13,16],480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid619 : RecordDataValid section14Catalog 16 (⟨119,(15),[4,8,12,16],[10],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid620 : RecordDataValid section14Catalog 16 (⟨119,(16),[4,8,12,16],[10],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid621 : RecordDataValid section14Catalog 16 (⟨119,(17),[4,8,12,16],[10],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid622 : RecordDataValid section14Catalog 16 (⟨119,(18),[4,8,12,16],[10],721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨721,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],722⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid623 : RecordDataValid section14Catalog 16 (⟨119,(19),[4,8,12,16],[10],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid624 : RecordDataValid section14Catalog 16 (⟨119,(20),[4,8,12,16],[10],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid625 : RecordDataValid section14Catalog 16 (⟨119,(21),[4,8,12,16],[10],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid626 : RecordDataValid section14Catalog 16 (⟨119,(22),[4,8,12,16],[10],478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨478,[1,4,5,6,8,9,10,12,13,16],479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid627 : RecordDataValid section14Catalog 16 (⟨119,(23),[4,8,12,16],[10],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid628 : RecordDataValid section14Catalog 16 (⟨119,(24),[4,8,12,16],[10],479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨479,[1,4,5,6,8,9,10,12,13,16],480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid629 : RecordDataValid section14Catalog 16 (⟨121,(0),[4,8,12,16],[10],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid630 : RecordDataValid section14Catalog 16 (⟨121,(1),[4,8,12,16],[10],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid631 : RecordDataValid section14Catalog 16 (⟨121,(2),[4,8,12,16],[10],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid632 : RecordDataValid section14Catalog 16 (⟨121,(3),[4,8,12,16],[10],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid633 : RecordDataValid section14Catalog 16 (⟨121,(4),[4,8,12,16],[10],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid634 : RecordDataValid section14Catalog 16 (⟨121,(5),[4,8,12,16],[10],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid635 : RecordDataValid section14Catalog 16 (⟨121,(6),[4,8,12,16],[10],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid636 : RecordDataValid section14Catalog 16 (⟨121,(7),[4,8,12,16],[10],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid637 : RecordDataValid section14Catalog 16 (⟨121,(8),[4,8,12,16],[10],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid638 : RecordDataValid section14Catalog 16 (⟨121,(9),[4,8,12,16],[10],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid639 : RecordDataValid section14Catalog 16 (⟨121,(10),[4,8,12,16],[10],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 608).take 32 = [⟨119,(4),[4,8,12,16],[10],474⟩,⟨119,(5),[4,8,12,16],[10],475⟩,⟨119,(6),[4,8,12,16],[10],475⟩,⟨119,(7),[4,8,12,16],[10],475⟩,⟨119,(8),[4,8,12,16],[10],714⟩,⟨119,(9),[4,8,12,16],[10],475⟩,⟨119,(10),[4,8,12,16],[10],476⟩,⟨119,(11),[4,8,12,16],[10],477⟩,⟨119,(12),[4,8,12,16],[10],478⟩,⟨119,(13),[4,8,12,16],[10],718⟩,⟨119,(14),[4,8,12,16],[10],479⟩,⟨119,(15),[4,8,12,16],[10],476⟩,⟨119,(16),[4,8,12,16],[10],480⟩,⟨119,(17),[4,8,12,16],[10],480⟩,⟨119,(18),[4,8,12,16],[10],721⟩,⟨119,(19),[4,8,12,16],[10],480⟩,⟨119,(20),[4,8,12,16],[10],476⟩,⟨119,(21),[4,8,12,16],[10],477⟩,⟨119,(22),[4,8,12,16],[10],478⟩,⟨119,(23),[4,8,12,16],[10],718⟩,⟨119,(24),[4,8,12,16],[10],479⟩,⟨121,(0),[4,8,12,16],[10],481⟩,⟨121,(1),[4,8,12,16],[10],482⟩,⟨121,(2),[4,8,12,16],[10],481⟩,⟨121,(3),[4,8,12,16],[10],483⟩,⟨121,(4),[4,8,12,16],[10],484⟩,⟨121,(5),[4,8,12,16],[10],481⟩,⟨121,(6),[4,8,12,16],[10],482⟩,⟨121,(7),[4,8,12,16],[10],481⟩,⟨121,(8),[4,8,12,16],[10],483⟩,⟨121,(9),[4,8,12,16],[10],484⟩,⟨121,(10),[4,8,12,16],[10],485⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid608
  · exact recordValid_of_data section14Catalog 16 _ hnum valid609
  · exact recordValid_of_data section14Catalog 16 _ hnum valid610
  · exact recordValid_of_data section14Catalog 16 _ hnum valid611
  · exact recordValid_of_data section14Catalog 16 _ hnum valid612
  · exact recordValid_of_data section14Catalog 16 _ hnum valid613
  · exact recordValid_of_data section14Catalog 16 _ hnum valid614
  · exact recordValid_of_data section14Catalog 16 _ hnum valid615
  · exact recordValid_of_data section14Catalog 16 _ hnum valid616
  · exact recordValid_of_data section14Catalog 16 _ hnum valid617
  · exact recordValid_of_data section14Catalog 16 _ hnum valid618
  · exact recordValid_of_data section14Catalog 16 _ hnum valid619
  · exact recordValid_of_data section14Catalog 16 _ hnum valid620
  · exact recordValid_of_data section14Catalog 16 _ hnum valid621
  · exact recordValid_of_data section14Catalog 16 _ hnum valid622
  · exact recordValid_of_data section14Catalog 16 _ hnum valid623
  · exact recordValid_of_data section14Catalog 16 _ hnum valid624
  · exact recordValid_of_data section14Catalog 16 _ hnum valid625
  · exact recordValid_of_data section14Catalog 16 _ hnum valid626
  · exact recordValid_of_data section14Catalog 16 _ hnum valid627
  · exact recordValid_of_data section14Catalog 16 _ hnum valid628
  · exact recordValid_of_data section14Catalog 16 _ hnum valid629
  · exact recordValid_of_data section14Catalog 16 _ hnum valid630
  · exact recordValid_of_data section14Catalog 16 _ hnum valid631
  · exact recordValid_of_data section14Catalog 16 _ hnum valid632
  · exact recordValid_of_data section14Catalog 16 _ hnum valid633
  · exact recordValid_of_data section14Catalog 16 _ hnum valid634
  · exact recordValid_of_data section14Catalog 16 _ hnum valid635
  · exact recordValid_of_data section14Catalog 16 _ hnum valid636
  · exact recordValid_of_data section14Catalog 16 _ hnum valid637
  · exact recordValid_of_data section14Catalog 16 _ hnum valid638
  · exact recordValid_of_data section14Catalog 16 _ hnum valid639
end Section14Records_16_608_640

#print axioms solution
