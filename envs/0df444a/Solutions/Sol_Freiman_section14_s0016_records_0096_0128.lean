-- Prove2me | solution 1 for Freiman.section14_s0016_records_0096_0128
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T22:37:04.458176+00:00
-- url     : https://prove2.me/submissions/dd4eb6d6-3d9a-42b4-a941-ffad460af970

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
namespace Section14Records_16_96_128
private theorem valid96 : RecordDataValid section14Catalog 16 (⟨20,(11),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid97 : RecordDataValid section14Catalog 16 (⟨20,(11),[4,16],[14],213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨213,[1,2,3,4,13,14,15,16],213⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid98 : RecordDataValid section14Catalog 16 (⟨20,(12),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid99 : RecordDataValid section14Catalog 16 (⟨20,(12),[4,16],[14],213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨213,[1,2,3,4,13,14,15,16],213⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid100 : RecordDataValid section14Catalog 16 (⟨20,(13),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid101 : RecordDataValid section14Catalog 16 (⟨20,(13),[4,16],[14],213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨213,[1,2,3,4,13,14,15,16],213⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid102 : RecordDataValid section14Catalog 16 (⟨20,(14),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid103 : RecordDataValid section14Catalog 16 (⟨20,(14),[4,16],[14],212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨212,[1,2,3,4,11,13,14,15,16],212⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid104 : RecordDataValid section14Catalog 16 (⟨20,(15),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid105 : RecordDataValid section14Catalog 16 (⟨20,(15),[4,16],[14],214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨214,[1,2,3,4,13,14,15,16],214⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid106 : RecordDataValid section14Catalog 16 (⟨20,(16),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid107 : RecordDataValid section14Catalog 16 (⟨20,(16),[4,16],[14],214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨214,[1,2,3,4,13,14,15,16],214⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid108 : RecordDataValid section14Catalog 16 (⟨20,(17),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid109 : RecordDataValid section14Catalog 16 (⟨20,(17),[4,16],[14],214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨214,[1,2,3,4,13,14,15,16],214⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid110 : RecordDataValid section14Catalog 16 (⟨20,(18),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid111 : RecordDataValid section14Catalog 16 (⟨20,(18),[4,16],[14],214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨214,[1,2,3,4,13,14,15,16],214⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid112 : RecordDataValid section14Catalog 16 (⟨20,(19),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid113 : RecordDataValid section14Catalog 16 (⟨20,(19),[4,16],[14],214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨214,[1,2,3,4,13,14,15,16],214⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid114 : RecordDataValid section14Catalog 16 (⟨20,(20),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid115 : RecordDataValid section14Catalog 16 (⟨20,(20),[4,16],[14],215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨215,[1,2,3,4,13,14,15,16],215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid116 : RecordDataValid section14Catalog 16 (⟨20,(21),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid117 : RecordDataValid section14Catalog 16 (⟨20,(21),[4,16],[14],215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨215,[1,2,3,4,13,14,15,16],215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid118 : RecordDataValid section14Catalog 16 (⟨20,(22),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid119 : RecordDataValid section14Catalog 16 (⟨20,(22),[4,16],[14],215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨215,[1,2,3,4,13,14,15,16],215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid120 : RecordDataValid section14Catalog 16 (⟨20,(23),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid121 : RecordDataValid section14Catalog 16 (⟨20,(23),[4,16],[14],215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨215,[1,2,3,4,13,14,15,16],215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid122 : RecordDataValid section14Catalog 16 (⟨20,(24),[4,8,16],[6],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid123 : RecordDataValid section14Catalog 16 (⟨20,(24),[4,16],[14],215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨215,[1,2,3,4,13,14,15,16],215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid124 : RecordDataValid section14Catalog 16 (⟨25,(0),[4,8,12,16],[6],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid125 : RecordDataValid section14Catalog 16 (⟨25,(0),[4,16],[14],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid126 : RecordDataValid section14Catalog 16 (⟨25,(1),[4,16],[6],190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨190,[1,2,3,4,5,6,7,13,14,15,16],190⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid127 : RecordDataValid section14Catalog 16 (⟨25,(1),[4,16],[14],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 96).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 96).take 32 = [⟨20,(11),[4,8,16],[6],3⟩,⟨20,(11),[4,16],[14],213⟩,⟨20,(12),[4,8,16],[6],3⟩,⟨20,(12),[4,16],[14],213⟩,⟨20,(13),[4,8,16],[6],3⟩,⟨20,(13),[4,16],[14],213⟩,⟨20,(14),[4,8,16],[6],3⟩,⟨20,(14),[4,16],[14],212⟩,⟨20,(15),[4,8,16],[6],3⟩,⟨20,(15),[4,16],[14],214⟩,⟨20,(16),[4,8,16],[6],3⟩,⟨20,(16),[4,16],[14],214⟩,⟨20,(17),[4,8,16],[6],3⟩,⟨20,(17),[4,16],[14],214⟩,⟨20,(18),[4,8,16],[6],3⟩,⟨20,(18),[4,16],[14],214⟩,⟨20,(19),[4,8,16],[6],3⟩,⟨20,(19),[4,16],[14],214⟩,⟨20,(20),[4,8,16],[6],3⟩,⟨20,(20),[4,16],[14],215⟩,⟨20,(21),[4,8,16],[6],3⟩,⟨20,(21),[4,16],[14],215⟩,⟨20,(22),[4,8,16],[6],3⟩,⟨20,(22),[4,16],[14],215⟩,⟨20,(23),[4,8,16],[6],3⟩,⟨20,(23),[4,16],[14],215⟩,⟨20,(24),[4,8,16],[6],3⟩,⟨20,(24),[4,16],[14],215⟩,⟨25,(0),[4,8,12,16],[6],189⟩,⟨25,(0),[4,16],[14],189⟩,⟨25,(1),[4,16],[6],190⟩,⟨25,(1),[4,16],[14],260⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid96
  · exact recordValid_of_data section14Catalog 16 _ hnum valid97
  · exact recordValid_of_data section14Catalog 16 _ hnum valid98
  · exact recordValid_of_data section14Catalog 16 _ hnum valid99
  · exact recordValid_of_data section14Catalog 16 _ hnum valid100
  · exact recordValid_of_data section14Catalog 16 _ hnum valid101
  · exact recordValid_of_data section14Catalog 16 _ hnum valid102
  · exact recordValid_of_data section14Catalog 16 _ hnum valid103
  · exact recordValid_of_data section14Catalog 16 _ hnum valid104
  · exact recordValid_of_data section14Catalog 16 _ hnum valid105
  · exact recordValid_of_data section14Catalog 16 _ hnum valid106
  · exact recordValid_of_data section14Catalog 16 _ hnum valid107
  · exact recordValid_of_data section14Catalog 16 _ hnum valid108
  · exact recordValid_of_data section14Catalog 16 _ hnum valid109
  · exact recordValid_of_data section14Catalog 16 _ hnum valid110
  · exact recordValid_of_data section14Catalog 16 _ hnum valid111
  · exact recordValid_of_data section14Catalog 16 _ hnum valid112
  · exact recordValid_of_data section14Catalog 16 _ hnum valid113
  · exact recordValid_of_data section14Catalog 16 _ hnum valid114
  · exact recordValid_of_data section14Catalog 16 _ hnum valid115
  · exact recordValid_of_data section14Catalog 16 _ hnum valid116
  · exact recordValid_of_data section14Catalog 16 _ hnum valid117
  · exact recordValid_of_data section14Catalog 16 _ hnum valid118
  · exact recordValid_of_data section14Catalog 16 _ hnum valid119
  · exact recordValid_of_data section14Catalog 16 _ hnum valid120
  · exact recordValid_of_data section14Catalog 16 _ hnum valid121
  · exact recordValid_of_data section14Catalog 16 _ hnum valid122
  · exact recordValid_of_data section14Catalog 16 _ hnum valid123
  · exact recordValid_of_data section14Catalog 16 _ hnum valid124
  · exact recordValid_of_data section14Catalog 16 _ hnum valid125
  · exact recordValid_of_data section14Catalog 16 _ hnum valid126
  · exact recordValid_of_data section14Catalog 16 _ hnum valid127
end Section14Records_16_96_128

#print axioms solution
