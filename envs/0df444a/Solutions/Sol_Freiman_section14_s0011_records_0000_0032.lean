-- Prove2me | solution 1 for Freiman.section14_s0011_records_0000_0032
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T09:47:46.081687+00:00
-- url     : https://prove2.me/submissions/99c39232-886e-4130-802c-c1d293b7ca7a

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
namespace Section14Records_11_0_32
private theorem valid0 : RecordDataValid section14Catalog 11 (⟨1,(-1),[1,3,5,7,9,11,13,15],[0],1⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1 : RecordDataValid section14Catalog 11 (⟨1,(-1),[4,8,11,12,16],[1],5⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨5,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],5⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2 : RecordDataValid section14Catalog 11 (⟨1,(-1),[11],[3],56⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨56,[1,2,3,5,6,7,9,10,11,13,14,15],56⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3 : RecordDataValid section14Catalog 11 (⟨16,(-1),[3,7,11,15],[0],914⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨914,[2,3,6,7,11,14,15],917⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4 : RecordDataValid section14Catalog 11 (⟨16,(-1),[11],[1],66⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨66,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],66⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid5 : RecordDataValid section14Catalog 11 (⟨16,(-1),[11],[3],242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨242,[1,2,3,5,6,7,9,10,11,13,14,15],242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid6 : RecordDataValid section14Catalog 11 (⟨25,(0),[11],[2],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid7 : RecordDataValid section14Catalog 11 (⟨25,(1),[11],[2],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid8 : RecordDataValid section14Catalog 11 (⟨25,(2),[11],[2],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid9 : RecordDataValid section14Catalog 11 (⟨25,(3),[11],[2],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid10 : RecordDataValid section14Catalog 11 (⟨25,(4),[11],[2],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid11 : RecordDataValid section14Catalog 11 (⟨25,(5),[11],[2],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid12 : RecordDataValid section14Catalog 11 (⟨25,(6),[11],[2],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid13 : RecordDataValid section14Catalog 11 (⟨25,(7),[11],[2],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid14 : RecordDataValid section14Catalog 11 (⟨25,(8),[11],[2],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid15 : RecordDataValid section14Catalog 11 (⟨25,(9),[11],[2],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid16 : RecordDataValid section14Catalog 11 (⟨25,(10),[11],[2],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid17 : RecordDataValid section14Catalog 11 (⟨25,(11),[11],[2],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid18 : RecordDataValid section14Catalog 11 (⟨25,(12),[11],[2],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid19 : RecordDataValid section14Catalog 11 (⟨25,(13),[11],[2],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid20 : RecordDataValid section14Catalog 11 (⟨25,(14),[11],[2],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid21 : RecordDataValid section14Catalog 11 (⟨25,(15),[11],[2],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid22 : RecordDataValid section14Catalog 11 (⟨25,(16),[11],[2],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid23 : RecordDataValid section14Catalog 11 (⟨25,(17),[11],[2],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid24 : RecordDataValid section14Catalog 11 (⟨25,(18),[11],[2],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid25 : RecordDataValid section14Catalog 11 (⟨25,(19),[11],[2],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid26 : RecordDataValid section14Catalog 11 (⟨25,(20),[11],[2],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid27 : RecordDataValid section14Catalog 11 (⟨25,(21),[11],[2],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid28 : RecordDataValid section14Catalog 11 (⟨25,(22),[11],[2],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid29 : RecordDataValid section14Catalog 11 (⟨25,(23),[11],[2],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid30 : RecordDataValid section14Catalog 11 (⟨25,(24),[11],[2],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid31 : RecordDataValid section14Catalog 11 (⟨30,(0),[11,12],[2],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 0).take 32, section14RecordValid section14Catalog 11 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (11 ∈ r.states))).drop 0).take 32 = [⟨1,(-1),[1,3,5,7,9,11,13,15],[0],1⟩,⟨1,(-1),[4,8,11,12,16],[1],5⟩,⟨1,(-1),[11],[3],56⟩,⟨16,(-1),[3,7,11,15],[0],914⟩,⟨16,(-1),[11],[1],66⟩,⟨16,(-1),[11],[3],242⟩,⟨25,(0),[11],[2],189⟩,⟨25,(1),[11],[2],216⟩,⟨25,(2),[11],[2],217⟩,⟨25,(3),[11],[2],218⟩,⟨25,(4),[11],[2],219⟩,⟨25,(5),[11],[2],189⟩,⟨25,(6),[11],[2],216⟩,⟨25,(7),[11],[2],217⟩,⟨25,(8),[11],[2],218⟩,⟨25,(9),[11],[2],219⟩,⟨25,(10),[11],[2],194⟩,⟨25,(11),[11],[2],220⟩,⟨25,(12),[11],[2],220⟩,⟨25,(13),[11],[2],220⟩,⟨25,(14),[11],[2],219⟩,⟨25,(15),[11],[2],196⟩,⟨25,(16),[11],[2],221⟩,⟨25,(17),[11],[2],221⟩,⟨25,(18),[11],[2],221⟩,⟨25,(19),[11],[2],221⟩,⟨25,(20),[11],[2],198⟩,⟨25,(21),[11],[2],222⟩,⟨25,(22),[11],[2],222⟩,⟨25,(23),[11],[2],222⟩,⟨25,(24),[11],[2],222⟩,⟨30,(0),[11,12],[2],152⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 11 _ hnum valid0
  · exact recordValid_of_data section14Catalog 11 _ hnum valid1
  · exact recordValid_of_data section14Catalog 11 _ hnum valid2
  · exact recordValid_of_data section14Catalog 11 _ hnum valid3
  · exact recordValid_of_data section14Catalog 11 _ hnum valid4
  · exact recordValid_of_data section14Catalog 11 _ hnum valid5
  · exact recordValid_of_data section14Catalog 11 _ hnum valid6
  · exact recordValid_of_data section14Catalog 11 _ hnum valid7
  · exact recordValid_of_data section14Catalog 11 _ hnum valid8
  · exact recordValid_of_data section14Catalog 11 _ hnum valid9
  · exact recordValid_of_data section14Catalog 11 _ hnum valid10
  · exact recordValid_of_data section14Catalog 11 _ hnum valid11
  · exact recordValid_of_data section14Catalog 11 _ hnum valid12
  · exact recordValid_of_data section14Catalog 11 _ hnum valid13
  · exact recordValid_of_data section14Catalog 11 _ hnum valid14
  · exact recordValid_of_data section14Catalog 11 _ hnum valid15
  · exact recordValid_of_data section14Catalog 11 _ hnum valid16
  · exact recordValid_of_data section14Catalog 11 _ hnum valid17
  · exact recordValid_of_data section14Catalog 11 _ hnum valid18
  · exact recordValid_of_data section14Catalog 11 _ hnum valid19
  · exact recordValid_of_data section14Catalog 11 _ hnum valid20
  · exact recordValid_of_data section14Catalog 11 _ hnum valid21
  · exact recordValid_of_data section14Catalog 11 _ hnum valid22
  · exact recordValid_of_data section14Catalog 11 _ hnum valid23
  · exact recordValid_of_data section14Catalog 11 _ hnum valid24
  · exact recordValid_of_data section14Catalog 11 _ hnum valid25
  · exact recordValid_of_data section14Catalog 11 _ hnum valid26
  · exact recordValid_of_data section14Catalog 11 _ hnum valid27
  · exact recordValid_of_data section14Catalog 11 _ hnum valid28
  · exact recordValid_of_data section14Catalog 11 _ hnum valid29
  · exact recordValid_of_data section14Catalog 11 _ hnum valid30
  · exact recordValid_of_data section14Catalog 11 _ hnum valid31
end Section14Records_11_0_32

#print axioms solution
