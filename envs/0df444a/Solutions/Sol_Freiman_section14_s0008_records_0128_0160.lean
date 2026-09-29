-- Prove2me | solution 1 for Freiman.section14_s0008_records_0128_0160
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:45:58.737735+00:00
-- url     : https://prove2.me/submissions/1642eca9-f36a-401d-9e19-600a12650341

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
namespace Section14Records_8_128_160
private theorem valid128 : RecordDataValid section14Catalog 8 (⟨20,(20),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid129 : RecordDataValid section14Catalog 8 (⟨20,(21),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid130 : RecordDataValid section14Catalog 8 (⟨20,(22),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid131 : RecordDataValid section14Catalog 8 (⟨20,(23),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid132 : RecordDataValid section14Catalog 8 (⟨20,(24),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid133 : RecordDataValid section14Catalog 8 (⟨25,(0),[4,8,12,16],[6],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid134 : RecordDataValid section14Catalog 8 (⟨25,(1),[8,12],[6],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid135 : RecordDataValid section14Catalog 8 (⟨25,(2),[8,12],[6],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid136 : RecordDataValid section14Catalog 8 (⟨25,(3),[8,12],[6],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid137 : RecordDataValid section14Catalog 8 (⟨25,(4),[8,12],[6],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid138 : RecordDataValid section14Catalog 8 (⟨25,(5),[4,8,12,16],[6],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid139 : RecordDataValid section14Catalog 8 (⟨25,(6),[8,12],[6],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid140 : RecordDataValid section14Catalog 8 (⟨25,(7),[8,12],[6],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid141 : RecordDataValid section14Catalog 8 (⟨25,(8),[8,12],[6],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid142 : RecordDataValid section14Catalog 8 (⟨25,(9),[8,12],[6],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid143 : RecordDataValid section14Catalog 8 (⟨25,(10),[4,8,12,16],[6],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid144 : RecordDataValid section14Catalog 8 (⟨25,(11),[8,12],[6],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid145 : RecordDataValid section14Catalog 8 (⟨25,(12),[8,12],[6],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid146 : RecordDataValid section14Catalog 8 (⟨25,(13),[8,12],[6],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid147 : RecordDataValid section14Catalog 8 (⟨25,(14),[8,12],[6],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid148 : RecordDataValid section14Catalog 8 (⟨25,(15),[4,8,12,16],[6],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid149 : RecordDataValid section14Catalog 8 (⟨25,(16),[8,12],[6],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid150 : RecordDataValid section14Catalog 8 (⟨25,(17),[8,12],[6],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid151 : RecordDataValid section14Catalog 8 (⟨25,(18),[8,12],[6],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid152 : RecordDataValid section14Catalog 8 (⟨25,(19),[8,12],[6],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid153 : RecordDataValid section14Catalog 8 (⟨25,(20),[4,8,12,16],[6],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid154 : RecordDataValid section14Catalog 8 (⟨25,(21),[8,12],[6],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid155 : RecordDataValid section14Catalog 8 (⟨25,(22),[8,12],[6],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid156 : RecordDataValid section14Catalog 8 (⟨25,(23),[8,12],[6],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid157 : RecordDataValid section14Catalog 8 (⟨25,(24),[8,12],[6],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid158 : RecordDataValid section14Catalog 8 (⟨30,(0),[4,8,12],[6],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid159 : RecordDataValid section14Catalog 8 (⟨30,(1),[4,8,12],[6],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 128).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 128).take 32 = [⟨20,(20),[4,8,16],[6],3⟩,⟨20,(21),[4,8,16],[6],3⟩,⟨20,(22),[4,8,16],[6],3⟩,⟨20,(23),[4,8,16],[6],3⟩,⟨20,(24),[4,8,16],[6],3⟩,⟨25,(0),[4,8,12,16],[6],189⟩,⟨25,(1),[8,12],[6],216⟩,⟨25,(2),[8,12],[6],217⟩,⟨25,(3),[8,12],[6],218⟩,⟨25,(4),[8,12],[6],219⟩,⟨25,(5),[4,8,12,16],[6],189⟩,⟨25,(6),[8,12],[6],216⟩,⟨25,(7),[8,12],[6],217⟩,⟨25,(8),[8,12],[6],218⟩,⟨25,(9),[8,12],[6],219⟩,⟨25,(10),[4,8,12,16],[6],194⟩,⟨25,(11),[8,12],[6],220⟩,⟨25,(12),[8,12],[6],220⟩,⟨25,(13),[8,12],[6],220⟩,⟨25,(14),[8,12],[6],219⟩,⟨25,(15),[4,8,12,16],[6],196⟩,⟨25,(16),[8,12],[6],221⟩,⟨25,(17),[8,12],[6],221⟩,⟨25,(18),[8,12],[6],221⟩,⟨25,(19),[8,12],[6],221⟩,⟨25,(20),[4,8,12,16],[6],198⟩,⟨25,(21),[8,12],[6],222⟩,⟨25,(22),[8,12],[6],222⟩,⟨25,(23),[8,12],[6],222⟩,⟨25,(24),[8,12],[6],222⟩,⟨30,(0),[4,8,12],[6],152⟩,⟨30,(1),[4,8,12],[6],153⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid128
  · exact recordValid_of_data section14Catalog 8 _ hnum valid129
  · exact recordValid_of_data section14Catalog 8 _ hnum valid130
  · exact recordValid_of_data section14Catalog 8 _ hnum valid131
  · exact recordValid_of_data section14Catalog 8 _ hnum valid132
  · exact recordValid_of_data section14Catalog 8 _ hnum valid133
  · exact recordValid_of_data section14Catalog 8 _ hnum valid134
  · exact recordValid_of_data section14Catalog 8 _ hnum valid135
  · exact recordValid_of_data section14Catalog 8 _ hnum valid136
  · exact recordValid_of_data section14Catalog 8 _ hnum valid137
  · exact recordValid_of_data section14Catalog 8 _ hnum valid138
  · exact recordValid_of_data section14Catalog 8 _ hnum valid139
  · exact recordValid_of_data section14Catalog 8 _ hnum valid140
  · exact recordValid_of_data section14Catalog 8 _ hnum valid141
  · exact recordValid_of_data section14Catalog 8 _ hnum valid142
  · exact recordValid_of_data section14Catalog 8 _ hnum valid143
  · exact recordValid_of_data section14Catalog 8 _ hnum valid144
  · exact recordValid_of_data section14Catalog 8 _ hnum valid145
  · exact recordValid_of_data section14Catalog 8 _ hnum valid146
  · exact recordValid_of_data section14Catalog 8 _ hnum valid147
  · exact recordValid_of_data section14Catalog 8 _ hnum valid148
  · exact recordValid_of_data section14Catalog 8 _ hnum valid149
  · exact recordValid_of_data section14Catalog 8 _ hnum valid150
  · exact recordValid_of_data section14Catalog 8 _ hnum valid151
  · exact recordValid_of_data section14Catalog 8 _ hnum valid152
  · exact recordValid_of_data section14Catalog 8 _ hnum valid153
  · exact recordValid_of_data section14Catalog 8 _ hnum valid154
  · exact recordValid_of_data section14Catalog 8 _ hnum valid155
  · exact recordValid_of_data section14Catalog 8 _ hnum valid156
  · exact recordValid_of_data section14Catalog 8 _ hnum valid157
  · exact recordValid_of_data section14Catalog 8 _ hnum valid158
  · exact recordValid_of_data section14Catalog 8 _ hnum valid159
end Section14Records_8_128_160

#print axioms solution
