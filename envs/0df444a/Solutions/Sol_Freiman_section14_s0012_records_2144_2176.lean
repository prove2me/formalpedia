-- Prove2me | solution 1 for Freiman.section14_s0012_records_2144_2176
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:23:29.762984+00:00
-- url     : https://prove2.me/submissions/5bfaf854-d2bc-40ae-aed1-814cdd3de544

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
namespace Section14Records_12_2144_2176
private theorem valid2144 : RecordDataValid section14Catalog 12 (⟨317,(12),[8,12],[10],1496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1496,[5,8,9,12],1501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2145 : RecordDataValid section14Catalog 12 (⟨317,(13),[8,12],[10],1493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1493,[5,8,9,12],1498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2146 : RecordDataValid section14Catalog 12 (⟨317,(14),[8,12],[10],1494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1494,[5,8,9,12],1499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2147 : RecordDataValid section14Catalog 12 (⟨317,(15),[8,12],[10],1495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1495,[5,8,9,12],1500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2148 : RecordDataValid section14Catalog 12 (⟨318,(0),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2149 : RecordDataValid section14Catalog 12 (⟨318,(1),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2150 : RecordDataValid section14Catalog 12 (⟨318,(2),[8,12],[10],1498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1498,[5,8,9,12],1503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2151 : RecordDataValid section14Catalog 12 (⟨318,(3),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2152 : RecordDataValid section14Catalog 12 (⟨318,(4),[8,12],[10],1498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1498,[5,8,9,12],1503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2153 : RecordDataValid section14Catalog 12 (⟨318,(5),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2154 : RecordDataValid section14Catalog 12 (⟨318,(6),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2155 : RecordDataValid section14Catalog 12 (⟨318,(7),[8,12],[10],1499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1499,[5,8,9,12],1504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2156 : RecordDataValid section14Catalog 12 (⟨318,(8),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2157 : RecordDataValid section14Catalog 12 (⟨318,(9),[8,12],[10],1499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1499,[5,8,9,12],1504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2158 : RecordDataValid section14Catalog 12 (⟨318,(10),[8,12],[10],1500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1500,[5,8,9,12],1505⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2159 : RecordDataValid section14Catalog 12 (⟨318,(11),[8,12],[10],1501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1501,[5,8,9,12],1506⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2160 : RecordDataValid section14Catalog 12 (⟨318,(12),[8,12],[10],1502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1502,[5,8,9,12],1507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2161 : RecordDataValid section14Catalog 12 (⟨318,(13),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2162 : RecordDataValid section14Catalog 12 (⟨318,(14),[8,12],[10],1502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1502,[5,8,9,12],1507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2163 : RecordDataValid section14Catalog 12 (⟨318,(15),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2164 : RecordDataValid section14Catalog 12 (⟨318,(16),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2165 : RecordDataValid section14Catalog 12 (⟨318,(17),[8,12],[10],1503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1503,[5,8,9,12],1508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2166 : RecordDataValid section14Catalog 12 (⟨318,(18),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2167 : RecordDataValid section14Catalog 12 (⟨318,(19),[8,12],[10],1503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1503,[5,8,9,12],1508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2168 : RecordDataValid section14Catalog 12 (⟨319,(0),[8,12],[10],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2169 : RecordDataValid section14Catalog 12 (⟨319,(1),[8,12],[10],1229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1229,[3,5,7,8,9,11,12,15],1233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2170 : RecordDataValid section14Catalog 12 (⟨319,(2),[8,12],[10],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2171 : RecordDataValid section14Catalog 12 (⟨319,(3),[8,12],[10],1230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1230,[3,5,7,8,9,11,12,15],1234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2172 : RecordDataValid section14Catalog 12 (⟨319,(4),[8,12],[10],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2173 : RecordDataValid section14Catalog 12 (⟨319,(5),[8,12],[10],1232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1232,[3,5,7,8,9,11,12,15],1236⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2174 : RecordDataValid section14Catalog 12 (⟨319,(6),[8,12],[10],1504⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1504,[5,8,9,12],1509⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2175 : RecordDataValid section14Catalog 12 (⟨319,(7),[8,12],[10],1505⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1505,[5,8,9,12],1510⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2144).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2144).take 32 = [⟨317,(12),[8,12],[10],1496⟩,⟨317,(13),[8,12],[10],1493⟩,⟨317,(14),[8,12],[10],1494⟩,⟨317,(15),[8,12],[10],1495⟩,⟨318,(0),[8,12],[10],882⟩,⟨318,(1),[8,12],[10],1497⟩,⟨318,(2),[8,12],[10],1498⟩,⟨318,(3),[8,12],[10],101⟩,⟨318,(4),[8,12],[10],1498⟩,⟨318,(5),[8,12],[10],882⟩,⟨318,(6),[8,12],[10],1497⟩,⟨318,(7),[8,12],[10],1499⟩,⟨318,(8),[8,12],[10],101⟩,⟨318,(9),[8,12],[10],1499⟩,⟨318,(10),[8,12],[10],1500⟩,⟨318,(11),[8,12],[10],1501⟩,⟨318,(12),[8,12],[10],1502⟩,⟨318,(13),[8,12],[10],101⟩,⟨318,(14),[8,12],[10],1502⟩,⟨318,(15),[8,12],[10],882⟩,⟨318,(16),[8,12],[10],1497⟩,⟨318,(17),[8,12],[10],1503⟩,⟨318,(18),[8,12],[10],101⟩,⟨318,(19),[8,12],[10],1503⟩,⟨319,(0),[8,12],[10],1231⟩,⟨319,(1),[8,12],[10],1229⟩,⟨319,(2),[8,12],[10],1228⟩,⟨319,(3),[8,12],[10],1230⟩,⟨319,(4),[8,12],[10],1231⟩,⟨319,(5),[8,12],[10],1232⟩,⟨319,(6),[8,12],[10],1504⟩,⟨319,(7),[8,12],[10],1505⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2144
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2145
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2146
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2147
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2148
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2149
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2150
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2151
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2152
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2153
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2154
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2155
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2156
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2157
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2158
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2159
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2160
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2161
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2162
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2163
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2164
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2165
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2166
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2167
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2168
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2169
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2170
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2171
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2172
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2173
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2174
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2175
end Section14Records_12_2144_2176

#print axioms solution
