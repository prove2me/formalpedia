-- Prove2me | solution 1 for Freiman.section14_s0008_records_0576_0608
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:02:56.938444+00:00
-- url     : https://prove2.me/submissions/7e5c2b3f-e233-401f-9883-bcf850fbbe00

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
namespace Section14Records_8_576_608
private theorem valid576 : RecordDataValid section14Catalog 8 (⟨92,(6),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid577 : RecordDataValid section14Catalog 8 (⟨92,(7),[4,8,12,16],[10],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid578 : RecordDataValid section14Catalog 8 (⟨92,(8),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid579 : RecordDataValid section14Catalog 8 (⟨92,(9),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid580 : RecordDataValid section14Catalog 8 (⟨92,(10),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid581 : RecordDataValid section14Catalog 8 (⟨92,(11),[4,8,12,16],[10],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid582 : RecordDataValid section14Catalog 8 (⟨92,(12),[4,8,12,16],[10],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid583 : RecordDataValid section14Catalog 8 (⟨92,(13),[4,8,12,16],[10],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid584 : RecordDataValid section14Catalog 8 (⟨92,(14),[4,8,12,16],[10],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid585 : RecordDataValid section14Catalog 8 (⟨92,(15),[4,8,12,16],[10],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid586 : RecordDataValid section14Catalog 8 (⟨95,(0),[4,8,12,16],[10],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid587 : RecordDataValid section14Catalog 8 (⟨95,(1),[4,8,12,16],[10],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid588 : RecordDataValid section14Catalog 8 (⟨95,(2),[4,8,12,16],[10],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid589 : RecordDataValid section14Catalog 8 (⟨95,(3),[4,8,12,16],[10],412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid590 : RecordDataValid section14Catalog 8 (⟨95,(4),[4,8,12,16],[10],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid591 : RecordDataValid section14Catalog 8 (⟨95,(5),[4,8,12,16],[10],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid592 : RecordDataValid section14Catalog 8 (⟨95,(6),[4,8,12,16],[10],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid593 : RecordDataValid section14Catalog 8 (⟨95,(7),[4,8,12,16],[10],413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid594 : RecordDataValid section14Catalog 8 (⟨95,(8),[4,8,12,16],[10],414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨414,[1,4,5,6,8,9,10,12,13,16],415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid595 : RecordDataValid section14Catalog 8 (⟨95,(9),[4,8,12,16],[10],415⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨415,[1,4,5,6,8,9,10,12,13,16],416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid596 : RecordDataValid section14Catalog 8 (⟨95,(10),[4,8,12,16],[10],414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨414,[1,4,5,6,8,9,10,12,13,16],415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid597 : RecordDataValid section14Catalog 8 (⟨95,(11),[4,8,12,16],[10],416⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨416,[1,4,5,6,8,9,10,12,13,16],417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid598 : RecordDataValid section14Catalog 8 (⟨95,(12),[4,8,12,16],[10],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid599 : RecordDataValid section14Catalog 8 (⟨95,(13),[4,8,12,16],[10],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid600 : RecordDataValid section14Catalog 8 (⟨95,(14),[4,8,12,16],[10],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid601 : RecordDataValid section14Catalog 8 (⟨95,(15),[4,8,12,16],[10],417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid602 : RecordDataValid section14Catalog 8 (⟨96,(0),[4,8,12,16],[10],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid603 : RecordDataValid section14Catalog 8 (⟨96,(1),[4,8,12,16],[10],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid604 : RecordDataValid section14Catalog 8 (⟨96,(2),[4,8,12,16],[10],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid605 : RecordDataValid section14Catalog 8 (⟨96,(3),[4,8,12,16],[10],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid606 : RecordDataValid section14Catalog 8 (⟨96,(4),[4,8,12,16],[10],422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid607 : RecordDataValid section14Catalog 8 (⟨96,(5),[4,8,12,16],[10],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 576).take 32 = [⟨92,(6),[4,8,12,16],[10],409⟩,⟨92,(7),[4,8,12,16],[10],409⟩,⟨92,(8),[4,8,12,16],[10],410⟩,⟨92,(9),[4,8,12,16],[10],410⟩,⟨92,(10),[4,8,12,16],[10],410⟩,⟨92,(11),[4,8,12,16],[10],410⟩,⟨92,(12),[4,8,12,16],[10],411⟩,⟨92,(13),[4,8,12,16],[10],411⟩,⟨92,(14),[4,8,12,16],[10],411⟩,⟨92,(15),[4,8,12,16],[10],411⟩,⟨95,(0),[4,8,12,16],[10],412⟩,⟨95,(1),[4,8,12,16],[10],412⟩,⟨95,(2),[4,8,12,16],[10],412⟩,⟨95,(3),[4,8,12,16],[10],412⟩,⟨95,(4),[4,8,12,16],[10],413⟩,⟨95,(5),[4,8,12,16],[10],413⟩,⟨95,(6),[4,8,12,16],[10],413⟩,⟨95,(7),[4,8,12,16],[10],413⟩,⟨95,(8),[4,8,12,16],[10],414⟩,⟨95,(9),[4,8,12,16],[10],415⟩,⟨95,(10),[4,8,12,16],[10],414⟩,⟨95,(11),[4,8,12,16],[10],416⟩,⟨95,(12),[4,8,12,16],[10],417⟩,⟨95,(13),[4,8,12,16],[10],417⟩,⟨95,(14),[4,8,12,16],[10],417⟩,⟨95,(15),[4,8,12,16],[10],417⟩,⟨96,(0),[4,8,12,16],[10],418⟩,⟨96,(1),[4,8,12,16],[10],419⟩,⟨96,(2),[4,8,12,16],[10],420⟩,⟨96,(3),[4,8,12,16],[10],421⟩,⟨96,(4),[4,8,12,16],[10],422⟩,⟨96,(5),[4,8,12,16],[10],419⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid576
  · exact recordValid_of_data section14Catalog 8 _ hnum valid577
  · exact recordValid_of_data section14Catalog 8 _ hnum valid578
  · exact recordValid_of_data section14Catalog 8 _ hnum valid579
  · exact recordValid_of_data section14Catalog 8 _ hnum valid580
  · exact recordValid_of_data section14Catalog 8 _ hnum valid581
  · exact recordValid_of_data section14Catalog 8 _ hnum valid582
  · exact recordValid_of_data section14Catalog 8 _ hnum valid583
  · exact recordValid_of_data section14Catalog 8 _ hnum valid584
  · exact recordValid_of_data section14Catalog 8 _ hnum valid585
  · exact recordValid_of_data section14Catalog 8 _ hnum valid586
  · exact recordValid_of_data section14Catalog 8 _ hnum valid587
  · exact recordValid_of_data section14Catalog 8 _ hnum valid588
  · exact recordValid_of_data section14Catalog 8 _ hnum valid589
  · exact recordValid_of_data section14Catalog 8 _ hnum valid590
  · exact recordValid_of_data section14Catalog 8 _ hnum valid591
  · exact recordValid_of_data section14Catalog 8 _ hnum valid592
  · exact recordValid_of_data section14Catalog 8 _ hnum valid593
  · exact recordValid_of_data section14Catalog 8 _ hnum valid594
  · exact recordValid_of_data section14Catalog 8 _ hnum valid595
  · exact recordValid_of_data section14Catalog 8 _ hnum valid596
  · exact recordValid_of_data section14Catalog 8 _ hnum valid597
  · exact recordValid_of_data section14Catalog 8 _ hnum valid598
  · exact recordValid_of_data section14Catalog 8 _ hnum valid599
  · exact recordValid_of_data section14Catalog 8 _ hnum valid600
  · exact recordValid_of_data section14Catalog 8 _ hnum valid601
  · exact recordValid_of_data section14Catalog 8 _ hnum valid602
  · exact recordValid_of_data section14Catalog 8 _ hnum valid603
  · exact recordValid_of_data section14Catalog 8 _ hnum valid604
  · exact recordValid_of_data section14Catalog 8 _ hnum valid605
  · exact recordValid_of_data section14Catalog 8 _ hnum valid606
  · exact recordValid_of_data section14Catalog 8 _ hnum valid607
end Section14Records_8_576_608

#print axioms solution
