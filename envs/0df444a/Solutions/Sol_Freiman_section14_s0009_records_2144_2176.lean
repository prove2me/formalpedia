-- Prove2me | solution 1 for Freiman.section14_s0009_records_2144_2176
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:16:13.348239+00:00
-- url     : https://prove2.me/submissions/9174ed83-838b-412f-9357-72f7941cb898

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
namespace Section14Records_9_2144_2176
private theorem valid2144 : RecordDataValid section14Catalog 9 (⟨227,(22),[9],[42],1374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1374,[4,8,9,12,16],1378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2145 : RecordDataValid section14Catalog 9 (⟨227,(23),[9,10],[42],788⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2146 : RecordDataValid section14Catalog 9 (⟨227,(24),[9],[42],1374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1374,[4,8,9,12,16],1378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2147 : RecordDataValid section14Catalog 9 (⟨228,(0),[9,10],[42],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2148 : RecordDataValid section14Catalog 9 (⟨228,(1),[9,10],[42],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2149 : RecordDataValid section14Catalog 9 (⟨228,(2),[9,10],[42],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2150 : RecordDataValid section14Catalog 9 (⟨228,(3),[9,10],[42],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2151 : RecordDataValid section14Catalog 9 (⟨228,(4),[9,10],[42],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2152 : RecordDataValid section14Catalog 9 (⟨228,(5),[9,10],[42],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2153 : RecordDataValid section14Catalog 9 (⟨228,(6),[9,10],[42],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2154 : RecordDataValid section14Catalog 9 (⟨228,(7),[9,10],[42],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2155 : RecordDataValid section14Catalog 9 (⟨228,(8),[9,10],[42],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2156 : RecordDataValid section14Catalog 9 (⟨228,(9),[9,10],[42],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2157 : RecordDataValid section14Catalog 9 (⟨228,(10),[9,10],[42],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2158 : RecordDataValid section14Catalog 9 (⟨228,(11),[9,10],[42],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2159 : RecordDataValid section14Catalog 9 (⟨228,(12),[9,10],[42],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2160 : RecordDataValid section14Catalog 9 (⟨228,(13),[9,10],[42],801⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2161 : RecordDataValid section14Catalog 9 (⟨228,(14),[9,10],[42],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2162 : RecordDataValid section14Catalog 9 (⟨228,(15),[9,10],[42],802⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2163 : RecordDataValid section14Catalog 9 (⟨228,(16),[9,10],[42],803⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2164 : RecordDataValid section14Catalog 9 (⟨228,(17),[9,10],[42],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2165 : RecordDataValid section14Catalog 9 (⟨228,(18),[9,10],[42],805⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2166 : RecordDataValid section14Catalog 9 (⟨228,(19),[9,10],[42],804⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2167 : RecordDataValid section14Catalog 9 (⟨228,(20),[9,10],[42],806⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2168 : RecordDataValid section14Catalog 9 (⟨228,(21),[9,10],[42],807⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2169 : RecordDataValid section14Catalog 9 (⟨228,(22),[9,10],[42],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2170 : RecordDataValid section14Catalog 9 (⟨228,(23),[9,10],[42],809⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2171 : RecordDataValid section14Catalog 9 (⟨228,(24),[9,10],[42],808⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2172 : RecordDataValid section14Catalog 9 (⟨230,(0),[9,10],[42],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2173 : RecordDataValid section14Catalog 9 (⟨230,(1),[9,10],[42],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2174 : RecordDataValid section14Catalog 9 (⟨230,(2),[9,10],[42],812⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2175 : RecordDataValid section14Catalog 9 (⟨230,(3),[9,10],[42],813⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2144).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2144).take 32 = [⟨227,(22),[9],[42],1374⟩,⟨227,(23),[9,10],[42],788⟩,⟨227,(24),[9],[42],1374⟩,⟨228,(0),[9,10],[42],789⟩,⟨228,(1),[9,10],[42],790⟩,⟨228,(2),[9,10],[42],791⟩,⟨228,(3),[9,10],[42],792⟩,⟨228,(4),[9,10],[42],793⟩,⟨228,(5),[9,10],[42],794⟩,⟨228,(6),[9,10],[42],795⟩,⟨228,(7),[9,10],[42],796⟩,⟨228,(8),[9,10],[42],797⟩,⟨228,(9),[9,10],[42],793⟩,⟨228,(10),[9,10],[42],798⟩,⟨228,(11),[9,10],[42],799⟩,⟨228,(12),[9,10],[42],800⟩,⟨228,(13),[9,10],[42],801⟩,⟨228,(14),[9,10],[42],800⟩,⟨228,(15),[9,10],[42],802⟩,⟨228,(16),[9,10],[42],803⟩,⟨228,(17),[9,10],[42],804⟩,⟨228,(18),[9,10],[42],805⟩,⟨228,(19),[9,10],[42],804⟩,⟨228,(20),[9,10],[42],806⟩,⟨228,(21),[9,10],[42],807⟩,⟨228,(22),[9,10],[42],808⟩,⟨228,(23),[9,10],[42],809⟩,⟨228,(24),[9,10],[42],808⟩,⟨230,(0),[9,10],[42],810⟩,⟨230,(1),[9,10],[42],811⟩,⟨230,(2),[9,10],[42],812⟩,⟨230,(3),[9,10],[42],813⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2144
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2145
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2146
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2147
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2148
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2149
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2150
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2151
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2152
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2153
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2154
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2155
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2156
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2157
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2158
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2159
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2160
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2161
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2162
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2163
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2164
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2165
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2166
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2167
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2168
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2169
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2170
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2171
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2172
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2173
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2174
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2175
end Section14Records_9_2144_2176

#print axioms solution
