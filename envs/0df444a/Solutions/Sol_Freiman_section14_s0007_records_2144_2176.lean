-- Prove2me | solution 1 for Freiman.section14_s0007_records_2144_2176
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:33:18.74629+00:00
-- url     : https://prove2.me/submissions/3926350c-932b-422b-b486-a79fd98503f0

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
namespace Section14Records_7_2144_2176
private theorem valid2144 : RecordDataValid section14Catalog 7 (⟨372,(6),[3,7],[9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2145 : RecordDataValid section14Catalog 7 (⟨372,(6),[3,7,15],[11],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2146 : RecordDataValid section14Catalog 7 (⟨372,(7),[3,7],[9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2147 : RecordDataValid section14Catalog 7 (⟨372,(7),[3,7,15],[11],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2148 : RecordDataValid section14Catalog 7 (⟨372,(8),[3,7],[9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2149 : RecordDataValid section14Catalog 7 (⟨372,(8),[3,7,15],[11],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2150 : RecordDataValid section14Catalog 7 (⟨372,(9),[3,7],[9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2151 : RecordDataValid section14Catalog 7 (⟨372,(9),[3,7,15],[11],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2152 : RecordDataValid section14Catalog 7 (⟨376,(0),[7],[9],1541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1541,[7,11],1546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2153 : RecordDataValid section14Catalog 7 (⟨376,(0),[7],[11],1542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1542,[7],1547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2154 : RecordDataValid section14Catalog 7 (⟨376,(1),[3,7],[9],947⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨947,[3,7,11],951⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2155 : RecordDataValid section14Catalog 7 (⟨376,(1),[7],[11],1543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1543,[7],1548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2156 : RecordDataValid section14Catalog 7 (⟨376,(2),[3,7],[9],946⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨946,[3,7,11],950⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2157 : RecordDataValid section14Catalog 7 (⟨376,(2),[7],[11],1544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1544,[7],1549⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2158 : RecordDataValid section14Catalog 7 (⟨376,(3),[3,7],[9],948⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨948,[3,7,11],952⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2159 : RecordDataValid section14Catalog 7 (⟨376,(3),[7],[11],1545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1545,[7],1550⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2160 : RecordDataValid section14Catalog 7 (⟨379,(0),[7],[9,11],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2161 : RecordDataValid section14Catalog 7 (⟨379,(1),[3,7],[9],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2162 : RecordDataValid section14Catalog 7 (⟨379,(1),[3,7,15],[11],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2163 : RecordDataValid section14Catalog 7 (⟨379,(2),[3,7],[9],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2164 : RecordDataValid section14Catalog 7 (⟨379,(2),[3,7,15],[11],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2165 : RecordDataValid section14Catalog 7 (⟨379,(3),[3,7],[9],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2166 : RecordDataValid section14Catalog 7 (⟨379,(3),[3,7,15],[11],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2167 : RecordDataValid section14Catalog 7 (⟨381,(0),[3,7],[9],364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨364,[1,2,3,4,5,6,7,8,9,10,11,12],365⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2168 : RecordDataValid section14Catalog 7 (⟨381,(0),[7],[11],1405⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1405,[5,6,7,8,9,10,12],1410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2169 : RecordDataValid section14Catalog 7 (⟨381,(1),[3,7],[9],949⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨949,[3,7,11],953⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2170 : RecordDataValid section14Catalog 7 (⟨381,(1),[7],[11],1546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1546,[7],1551⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2171 : RecordDataValid section14Catalog 7 (⟨381,(2),[3,7],[11],945⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨945,[3,7,11],949⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2172 : RecordDataValid section14Catalog 7 (⟨381,(2),[7],[9],945⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨945,[3,7,11],949⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2173 : RecordDataValid section14Catalog 7 (⟨381,(3),[3,7],[11],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2174 : RecordDataValid section14Catalog 7 (⟨381,(3),[7],[9],939⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨939,[3,7,11],943⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2175 : RecordDataValid section14Catalog 7 (⟨381,(4),[3,7],[9],204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨204,[1,2,3,4,7],204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2144).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 2144).take 32 = [⟨372,(6),[3,7],[9],2⟩,⟨372,(6),[3,7,15],[11],2⟩,⟨372,(7),[3,7],[9],2⟩,⟨372,(7),[3,7,15],[11],2⟩,⟨372,(8),[3,7],[9],2⟩,⟨372,(8),[3,7,15],[11],2⟩,⟨372,(9),[3,7],[9],2⟩,⟨372,(9),[3,7,15],[11],2⟩,⟨376,(0),[7],[9],1541⟩,⟨376,(0),[7],[11],1542⟩,⟨376,(1),[3,7],[9],947⟩,⟨376,(1),[7],[11],1543⟩,⟨376,(2),[3,7],[9],946⟩,⟨376,(2),[7],[11],1544⟩,⟨376,(3),[3,7],[9],948⟩,⟨376,(3),[7],[11],1545⟩,⟨379,(0),[7],[9,11],2⟩,⟨379,(1),[3,7],[9],2⟩,⟨379,(1),[3,7,15],[11],2⟩,⟨379,(2),[3,7],[9],159⟩,⟨379,(2),[3,7,15],[11],159⟩,⟨379,(3),[3,7],[9],99⟩,⟨379,(3),[3,7,15],[11],99⟩,⟨381,(0),[3,7],[9],364⟩,⟨381,(0),[7],[11],1405⟩,⟨381,(1),[3,7],[9],949⟩,⟨381,(1),[7],[11],1546⟩,⟨381,(2),[3,7],[11],945⟩,⟨381,(2),[7],[9],945⟩,⟨381,(3),[3,7],[11],939⟩,⟨381,(3),[7],[9],939⟩,⟨381,(4),[3,7],[9],204⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2144
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2145
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2146
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2147
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2148
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2149
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2150
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2151
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2152
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2153
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2154
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2155
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2156
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2157
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2158
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2159
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2160
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2161
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2162
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2163
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2164
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2165
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2166
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2167
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2168
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2169
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2170
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2171
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2172
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2173
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2174
  · exact recordValid_of_data section14Catalog 7 _ hnum valid2175
end Section14Records_7_2144_2176

#print axioms solution
