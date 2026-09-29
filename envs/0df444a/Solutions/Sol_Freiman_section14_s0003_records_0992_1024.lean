-- Prove2me | solution 1 for Freiman.section14_s0003_records_0992_1024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T12:46:18.268188+00:00
-- url     : https://prove2.me/submissions/af154fba-1a11-4d9a-abf7-0759e633ec8d

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
namespace Section14Records_3_992_1024
private theorem valid992 : RecordDataValid section14Catalog 3 (⟨190,(21),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid993 : RecordDataValid section14Catalog 3 (⟨190,(21),[3,7],[11],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid994 : RecordDataValid section14Catalog 3 (⟨190,(22),[3,4,8,12,15,16],[10],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid995 : RecordDataValid section14Catalog 3 (⟨190,(22),[3,7],[11],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid996 : RecordDataValid section14Catalog 3 (⟨190,(23),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid997 : RecordDataValid section14Catalog 3 (⟨190,(23),[3,7],[11],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid998 : RecordDataValid section14Catalog 3 (⟨190,(24),[3,4,8,12,15,16],[10],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid999 : RecordDataValid section14Catalog 3 (⟨190,(24),[3,7],[11],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1000 : RecordDataValid section14Catalog 3 (⟨192,(0),[3,7],[11],1001⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1001,[3,5,6,7],1005⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1001 : RecordDataValid section14Catalog 3 (⟨192,(0),[3,7,15],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1002 : RecordDataValid section14Catalog 3 (⟨192,(1),[3,7],[11],1002⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1002,[3,5,6,7],1006⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1003 : RecordDataValid section14Catalog 3 (⟨192,(1),[3,7,15],[10],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1004 : RecordDataValid section14Catalog 3 (⟨192,(2),[3,7],[11],1001⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1001,[3,5,6,7],1005⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1005 : RecordDataValid section14Catalog 3 (⟨192,(2),[3,7,15],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1006 : RecordDataValid section14Catalog 3 (⟨192,(3),[3,7],[11],1003⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1003,[3,5,6,7],1007⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1007 : RecordDataValid section14Catalog 3 (⟨192,(3),[3,7,15],[10],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1008 : RecordDataValid section14Catalog 3 (⟨192,(4),[3,7],[11],1004⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1004,[3,5,6,7],1008⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1009 : RecordDataValid section14Catalog 3 (⟨192,(4),[3,7,15],[10],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1010 : RecordDataValid section14Catalog 3 (⟨192,(5),[3,7],[11],1001⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1001,[3,5,6,7],1005⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1011 : RecordDataValid section14Catalog 3 (⟨192,(5),[3,7,15],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1012 : RecordDataValid section14Catalog 3 (⟨192,(6),[3,7],[11],1002⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1002,[3,5,6,7],1006⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1013 : RecordDataValid section14Catalog 3 (⟨192,(6),[3,7,15],[10],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1014 : RecordDataValid section14Catalog 3 (⟨192,(7),[3,7],[11],1001⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1001,[3,5,6,7],1005⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1015 : RecordDataValid section14Catalog 3 (⟨192,(7),[3,7,15],[10],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1016 : RecordDataValid section14Catalog 3 (⟨192,(8),[3,7],[11],1003⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1003,[3,5,6,7],1007⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1017 : RecordDataValid section14Catalog 3 (⟨192,(8),[3,7,15],[10],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1018 : RecordDataValid section14Catalog 3 (⟨192,(9),[3,7],[11],1004⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1004,[3,5,6,7],1008⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1019 : RecordDataValid section14Catalog 3 (⟨192,(9),[3,7,15],[10],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1020 : RecordDataValid section14Catalog 3 (⟨192,(10),[3,7],[11],1005⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1005,[3,5,6,7],1009⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1021 : RecordDataValid section14Catalog 3 (⟨192,(10),[3,7,15],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1022 : RecordDataValid section14Catalog 3 (⟨192,(11),[3,7],[11],1005⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1005,[3,5,6,7],1009⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1023 : RecordDataValid section14Catalog 3 (⟨192,(11),[3,7,15],[10],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 992).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 992).take 32 = [⟨190,(21),[3,4,8,12,15,16],[10],693⟩,⟨190,(21),[3,7],[11],693⟩,⟨190,(22),[3,4,8,12,15,16],[10],694⟩,⟨190,(22),[3,7],[11],694⟩,⟨190,(23),[3,4,8,12,15,16],[10],693⟩,⟨190,(23),[3,7],[11],693⟩,⟨190,(24),[3,4,8,12,15,16],[10],695⟩,⟨190,(24),[3,7],[11],695⟩,⟨192,(0),[3,7],[11],1001⟩,⟨192,(0),[3,7,15],[10],441⟩,⟨192,(1),[3,7],[11],1002⟩,⟨192,(1),[3,7,15],[10],442⟩,⟨192,(2),[3,7],[11],1001⟩,⟨192,(2),[3,7,15],[10],441⟩,⟨192,(3),[3,7],[11],1003⟩,⟨192,(3),[3,7,15],[10],443⟩,⟨192,(4),[3,7],[11],1004⟩,⟨192,(4),[3,7,15],[10],444⟩,⟨192,(5),[3,7],[11],1001⟩,⟨192,(5),[3,7,15],[10],441⟩,⟨192,(6),[3,7],[11],1002⟩,⟨192,(6),[3,7,15],[10],442⟩,⟨192,(7),[3,7],[11],1001⟩,⟨192,(7),[3,7,15],[10],441⟩,⟨192,(8),[3,7],[11],1003⟩,⟨192,(8),[3,7,15],[10],443⟩,⟨192,(9),[3,7],[11],1004⟩,⟨192,(9),[3,7,15],[10],444⟩,⟨192,(10),[3,7],[11],1005⟩,⟨192,(10),[3,7,15],[10],445⟩,⟨192,(11),[3,7],[11],1005⟩,⟨192,(11),[3,7,15],[10],445⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid992
  · exact recordValid_of_data section14Catalog 3 _ hnum valid993
  · exact recordValid_of_data section14Catalog 3 _ hnum valid994
  · exact recordValid_of_data section14Catalog 3 _ hnum valid995
  · exact recordValid_of_data section14Catalog 3 _ hnum valid996
  · exact recordValid_of_data section14Catalog 3 _ hnum valid997
  · exact recordValid_of_data section14Catalog 3 _ hnum valid998
  · exact recordValid_of_data section14Catalog 3 _ hnum valid999
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1000
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1001
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1002
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1003
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1004
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1005
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1006
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1007
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1008
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1009
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1010
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1011
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1012
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1013
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1014
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1015
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1016
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1017
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1018
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1019
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1020
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1021
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1022
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1023
end Section14Records_3_992_1024

#print axioms solution
