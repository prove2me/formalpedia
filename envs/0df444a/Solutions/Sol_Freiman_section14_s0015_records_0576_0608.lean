-- Prove2me | solution 1 for Freiman.section14_s0015_records_0576_0608
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T18:56:33.638214+00:00
-- url     : https://prove2.me/submissions/c2b1d530-c6fa-4389-8175-c6c597fbaba7

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
namespace Section14Records_15_576_608
private theorem valid576 : RecordDataValid section14Catalog 15 (⟨183,(4),[3,7,15],[10],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid577 : RecordDataValid section14Catalog 15 (⟨183,(5),[3,7,15],[10],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid578 : RecordDataValid section14Catalog 15 (⟨183,(6),[3,7,15],[10],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid579 : RecordDataValid section14Catalog 15 (⟨183,(7),[3,7,15],[10],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid580 : RecordDataValid section14Catalog 15 (⟨183,(8),[3,7,15],[10],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid581 : RecordDataValid section14Catalog 15 (⟨183,(9),[3,7,15],[10],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid582 : RecordDataValid section14Catalog 15 (⟨183,(10),[3,7,15],[10],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid583 : RecordDataValid section14Catalog 15 (⟨183,(11),[3,7,15],[10],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid584 : RecordDataValid section14Catalog 15 (⟨183,(12),[3,7,15],[10],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid585 : RecordDataValid section14Catalog 15 (⟨183,(13),[3,7,15],[10],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid586 : RecordDataValid section14Catalog 15 (⟨183,(14),[3,7,15],[10],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid587 : RecordDataValid section14Catalog 15 (⟨183,(15),[3,7,15],[10],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid588 : RecordDataValid section14Catalog 15 (⟨185,(0),[3,4,8,12,15,16],[10],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid589 : RecordDataValid section14Catalog 15 (⟨185,(1),[3,4,8,12,15,16],[10],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid590 : RecordDataValid section14Catalog 15 (⟨185,(2),[3,4,8,12,15,16],[10],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid591 : RecordDataValid section14Catalog 15 (⟨185,(3),[3,4,8,12,15,16],[10],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid592 : RecordDataValid section14Catalog 15 (⟨185,(4),[3,4,8,12,15,16],[10],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid593 : RecordDataValid section14Catalog 15 (⟨185,(5),[3,4,8,12,15,16],[10],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid594 : RecordDataValid section14Catalog 15 (⟨185,(6),[3,4,8,12,15,16],[10],682⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨682,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],683⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid595 : RecordDataValid section14Catalog 15 (⟨185,(7),[3,4,8,12,15,16],[10],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid596 : RecordDataValid section14Catalog 15 (⟨185,(8),[3,4,8,12,15,16],[10],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid597 : RecordDataValid section14Catalog 15 (⟨185,(9),[3,4,8,12,15,16],[10],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid598 : RecordDataValid section14Catalog 15 (⟨185,(10),[3,4,8,12,15,16],[10],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid599 : RecordDataValid section14Catalog 15 (⟨185,(11),[3,4,8,12,15,16],[10],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid600 : RecordDataValid section14Catalog 15 (⟨185,(12),[3,4,8,12,15,16],[10],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid601 : RecordDataValid section14Catalog 15 (⟨185,(13),[3,4,8,12,15,16],[10],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid602 : RecordDataValid section14Catalog 15 (⟨185,(14),[3,4,8,12,15,16],[10],683⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨683,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],684⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid603 : RecordDataValid section14Catalog 15 (⟨185,(15),[3,4,8,12,15,16],[10],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid604 : RecordDataValid section14Catalog 15 (⟨188,(0),[3,7,15],[10],684⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨684,[1,2,3,5,6,7,10,11,13,14,15],685⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid605 : RecordDataValid section14Catalog 15 (⟨188,(1),[3,7,15],[10],685⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨685,[1,2,3,5,6,7,10,11,13,14,15],686⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid606 : RecordDataValid section14Catalog 15 (⟨188,(2),[3,7,15],[10],684⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨684,[1,2,3,5,6,7,10,11,13,14,15],685⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid607 : RecordDataValid section14Catalog 15 (⟨188,(3),[3,7,15],[10],686⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨686,[1,2,3,5,6,7,10,11,13,14,15],687⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 576).take 32 = [⟨183,(4),[3,7,15],[10],675⟩,⟨183,(5),[3,7,15],[10],675⟩,⟨183,(6),[3,7,15],[10],675⟩,⟨183,(7),[3,7,15],[10],675⟩,⟨183,(8),[3,7,15],[10],676⟩,⟨183,(9),[3,7,15],[10],676⟩,⟨183,(10),[3,7,15],[10],676⟩,⟨183,(11),[3,7,15],[10],676⟩,⟨183,(12),[3,7,15],[10],677⟩,⟨183,(13),[3,7,15],[10],677⟩,⟨183,(14),[3,7,15],[10],677⟩,⟨183,(15),[3,7,15],[10],677⟩,⟨185,(0),[3,4,8,12,15,16],[10],678⟩,⟨185,(1),[3,4,8,12,15,16],[10],679⟩,⟨185,(2),[3,4,8,12,15,16],[10],680⟩,⟨185,(3),[3,4,8,12,15,16],[10],681⟩,⟨185,(4),[3,4,8,12,15,16],[10],678⟩,⟨185,(5),[3,4,8,12,15,16],[10],679⟩,⟨185,(6),[3,4,8,12,15,16],[10],682⟩,⟨185,(7),[3,4,8,12,15,16],[10],681⟩,⟨185,(8),[3,4,8,12,15,16],[10],678⟩,⟨185,(9),[3,4,8,12,15,16],[10],679⟩,⟨185,(10),[3,4,8,12,15,16],[10],680⟩,⟨185,(11),[3,4,8,12,15,16],[10],681⟩,⟨185,(12),[3,4,8,12,15,16],[10],678⟩,⟨185,(13),[3,4,8,12,15,16],[10],679⟩,⟨185,(14),[3,4,8,12,15,16],[10],683⟩,⟨185,(15),[3,4,8,12,15,16],[10],681⟩,⟨188,(0),[3,7,15],[10],684⟩,⟨188,(1),[3,7,15],[10],685⟩,⟨188,(2),[3,7,15],[10],684⟩,⟨188,(3),[3,7,15],[10],686⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid576
  · exact recordValid_of_data section14Catalog 15 _ hnum valid577
  · exact recordValid_of_data section14Catalog 15 _ hnum valid578
  · exact recordValid_of_data section14Catalog 15 _ hnum valid579
  · exact recordValid_of_data section14Catalog 15 _ hnum valid580
  · exact recordValid_of_data section14Catalog 15 _ hnum valid581
  · exact recordValid_of_data section14Catalog 15 _ hnum valid582
  · exact recordValid_of_data section14Catalog 15 _ hnum valid583
  · exact recordValid_of_data section14Catalog 15 _ hnum valid584
  · exact recordValid_of_data section14Catalog 15 _ hnum valid585
  · exact recordValid_of_data section14Catalog 15 _ hnum valid586
  · exact recordValid_of_data section14Catalog 15 _ hnum valid587
  · exact recordValid_of_data section14Catalog 15 _ hnum valid588
  · exact recordValid_of_data section14Catalog 15 _ hnum valid589
  · exact recordValid_of_data section14Catalog 15 _ hnum valid590
  · exact recordValid_of_data section14Catalog 15 _ hnum valid591
  · exact recordValid_of_data section14Catalog 15 _ hnum valid592
  · exact recordValid_of_data section14Catalog 15 _ hnum valid593
  · exact recordValid_of_data section14Catalog 15 _ hnum valid594
  · exact recordValid_of_data section14Catalog 15 _ hnum valid595
  · exact recordValid_of_data section14Catalog 15 _ hnum valid596
  · exact recordValid_of_data section14Catalog 15 _ hnum valid597
  · exact recordValid_of_data section14Catalog 15 _ hnum valid598
  · exact recordValid_of_data section14Catalog 15 _ hnum valid599
  · exact recordValid_of_data section14Catalog 15 _ hnum valid600
  · exact recordValid_of_data section14Catalog 15 _ hnum valid601
  · exact recordValid_of_data section14Catalog 15 _ hnum valid602
  · exact recordValid_of_data section14Catalog 15 _ hnum valid603
  · exact recordValid_of_data section14Catalog 15 _ hnum valid604
  · exact recordValid_of_data section14Catalog 15 _ hnum valid605
  · exact recordValid_of_data section14Catalog 15 _ hnum valid606
  · exact recordValid_of_data section14Catalog 15 _ hnum valid607
end Section14Records_15_576_608

#print axioms solution
