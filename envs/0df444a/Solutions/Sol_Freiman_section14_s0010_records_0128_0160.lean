-- Prove2me | solution 1 for Freiman.section14_s0010_records_0128_0160
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T16:31:35.681608+00:00
-- url     : https://prove2.me/submissions/5dc4b47f-7d34-4b36-8e2f-d3342e499405

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
namespace Section14Records_10_128_160
private theorem valid128 : RecordDataValid section14Catalog 10 (⟨18,(7),[9,10],[38],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid129 : RecordDataValid section14Catalog 10 (⟨18,(7),[10],[34],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid130 : RecordDataValid section14Catalog 10 (⟨18,(8),[9,10],[38],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid131 : RecordDataValid section14Catalog 10 (⟨18,(8),[10],[34,35],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid132 : RecordDataValid section14Catalog 10 (⟨18,(9),[9,10],[35],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid133 : RecordDataValid section14Catalog 10 (⟨18,(9),[9,10],[38],161⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨161,[1,5,9,10,13],161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid134 : RecordDataValid section14Catalog 10 (⟨18,(9),[10],[34],107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid135 : RecordDataValid section14Catalog 10 (⟨18,(10),[9,10],[35],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid136 : RecordDataValid section14Catalog 10 (⟨18,(10),[9,10],[38],162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨162,[1,5,9,10,13],162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid137 : RecordDataValid section14Catalog 10 (⟨18,(10),[10],[34],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid138 : RecordDataValid section14Catalog 10 (⟨18,(11),[9,10],[35],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid139 : RecordDataValid section14Catalog 10 (⟨18,(11),[9,10],[38],163⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨163,[1,5,9,10,13],163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid140 : RecordDataValid section14Catalog 10 (⟨18,(11),[10],[34],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid141 : RecordDataValid section14Catalog 10 (⟨18,(12),[9,10],[35],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid142 : RecordDataValid section14Catalog 10 (⟨18,(12),[9,10],[38],164⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨164,[1,5,9,10,13],164⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid143 : RecordDataValid section14Catalog 10 (⟨18,(12),[10],[34],110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid144 : RecordDataValid section14Catalog 10 (⟨18,(13),[9,10],[38],163⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨163,[1,5,9,10,13],163⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid145 : RecordDataValid section14Catalog 10 (⟨18,(13),[10],[34,35],109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨109,[1,2,5,6,9,10,13,14],109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid146 : RecordDataValid section14Catalog 10 (⟨18,(14),[9,10],[35],111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨111,[1,2,5,6,9,10,13,14],111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid147 : RecordDataValid section14Catalog 10 (⟨18,(14),[9,10],[38],165⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨165,[1,5,9,10,13],165⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid148 : RecordDataValid section14Catalog 10 (⟨18,(14),[10],[34],111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨111,[1,2,5,6,9,10,13,14],111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid149 : RecordDataValid section14Catalog 10 (⟨18,(15),[9,10],[35],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid150 : RecordDataValid section14Catalog 10 (⟨18,(15),[9,10],[38],162⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨162,[1,5,9,10,13],162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid151 : RecordDataValid section14Catalog 10 (⟨18,(15),[10],[34],108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid152 : RecordDataValid section14Catalog 10 (⟨18,(16),[9,10],[35],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid153 : RecordDataValid section14Catalog 10 (⟨18,(16),[9,10],[38],166⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨166,[1,5,9,10,13],166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid154 : RecordDataValid section14Catalog 10 (⟨18,(16),[10],[34],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid155 : RecordDataValid section14Catalog 10 (⟨18,(17),[9,10],[35],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid156 : RecordDataValid section14Catalog 10 (⟨18,(17),[9,10],[38],166⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨166,[1,5,9,10,13],166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid157 : RecordDataValid section14Catalog 10 (⟨18,(17),[10],[34],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid158 : RecordDataValid section14Catalog 10 (⟨18,(18),[9,10],[38],166⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨166,[1,5,9,10,13],166⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid159 : RecordDataValid section14Catalog 10 (⟨18,(18),[10],[34,35],112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 128).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 128).take 32 = [⟨18,(7),[9,10],[38],161⟩,⟨18,(7),[10],[34],107⟩,⟨18,(8),[9,10],[38],161⟩,⟨18,(8),[10],[34,35],107⟩,⟨18,(9),[9,10],[35],107⟩,⟨18,(9),[9,10],[38],161⟩,⟨18,(9),[10],[34],107⟩,⟨18,(10),[9,10],[35],108⟩,⟨18,(10),[9,10],[38],162⟩,⟨18,(10),[10],[34],108⟩,⟨18,(11),[9,10],[35],109⟩,⟨18,(11),[9,10],[38],163⟩,⟨18,(11),[10],[34],109⟩,⟨18,(12),[9,10],[35],110⟩,⟨18,(12),[9,10],[38],164⟩,⟨18,(12),[10],[34],110⟩,⟨18,(13),[9,10],[38],163⟩,⟨18,(13),[10],[34,35],109⟩,⟨18,(14),[9,10],[35],111⟩,⟨18,(14),[9,10],[38],165⟩,⟨18,(14),[10],[34],111⟩,⟨18,(15),[9,10],[35],108⟩,⟨18,(15),[9,10],[38],162⟩,⟨18,(15),[10],[34],108⟩,⟨18,(16),[9,10],[35],112⟩,⟨18,(16),[9,10],[38],166⟩,⟨18,(16),[10],[34],112⟩,⟨18,(17),[9,10],[35],112⟩,⟨18,(17),[9,10],[38],166⟩,⟨18,(17),[10],[34],112⟩,⟨18,(18),[9,10],[38],166⟩,⟨18,(18),[10],[34,35],112⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid128
  · exact recordValid_of_data section14Catalog 10 _ hnum valid129
  · exact recordValid_of_data section14Catalog 10 _ hnum valid130
  · exact recordValid_of_data section14Catalog 10 _ hnum valid131
  · exact recordValid_of_data section14Catalog 10 _ hnum valid132
  · exact recordValid_of_data section14Catalog 10 _ hnum valid133
  · exact recordValid_of_data section14Catalog 10 _ hnum valid134
  · exact recordValid_of_data section14Catalog 10 _ hnum valid135
  · exact recordValid_of_data section14Catalog 10 _ hnum valid136
  · exact recordValid_of_data section14Catalog 10 _ hnum valid137
  · exact recordValid_of_data section14Catalog 10 _ hnum valid138
  · exact recordValid_of_data section14Catalog 10 _ hnum valid139
  · exact recordValid_of_data section14Catalog 10 _ hnum valid140
  · exact recordValid_of_data section14Catalog 10 _ hnum valid141
  · exact recordValid_of_data section14Catalog 10 _ hnum valid142
  · exact recordValid_of_data section14Catalog 10 _ hnum valid143
  · exact recordValid_of_data section14Catalog 10 _ hnum valid144
  · exact recordValid_of_data section14Catalog 10 _ hnum valid145
  · exact recordValid_of_data section14Catalog 10 _ hnum valid146
  · exact recordValid_of_data section14Catalog 10 _ hnum valid147
  · exact recordValid_of_data section14Catalog 10 _ hnum valid148
  · exact recordValid_of_data section14Catalog 10 _ hnum valid149
  · exact recordValid_of_data section14Catalog 10 _ hnum valid150
  · exact recordValid_of_data section14Catalog 10 _ hnum valid151
  · exact recordValid_of_data section14Catalog 10 _ hnum valid152
  · exact recordValid_of_data section14Catalog 10 _ hnum valid153
  · exact recordValid_of_data section14Catalog 10 _ hnum valid154
  · exact recordValid_of_data section14Catalog 10 _ hnum valid155
  · exact recordValid_of_data section14Catalog 10 _ hnum valid156
  · exact recordValid_of_data section14Catalog 10 _ hnum valid157
  · exact recordValid_of_data section14Catalog 10 _ hnum valid158
  · exact recordValid_of_data section14Catalog 10 _ hnum valid159
end Section14Records_10_128_160

#print axioms solution
