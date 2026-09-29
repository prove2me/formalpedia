-- Prove2me | solution 1 for Freiman.section14_s0012_records_2176_2208
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:25:12.617646+00:00
-- url     : https://prove2.me/submissions/14463424-dbe7-4d43-a620-472271c00a2c

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
namespace Section14Records_12_2176_2208
private theorem valid2176 : RecordDataValid section14Catalog 12 (⟨319,(8),[8,12],[10],1235⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1235,[3,5,7,8,9,11,12,15],1239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2177 : RecordDataValid section14Catalog 12 (⟨319,(9),[8,12],[10],1236⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1236,[3,5,7,8,9,11,12,15],1240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2178 : RecordDataValid section14Catalog 12 (⟨319,(10),[8,12],[10],1506⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1506,[5,8,9,12],1511⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2179 : RecordDataValid section14Catalog 12 (⟨319,(11),[8,12],[10],1507⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1507,[5,8,9,12],1512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2180 : RecordDataValid section14Catalog 12 (⟨319,(12),[8,12],[10],1239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1239,[3,5,7,8,9,11,12,15],1243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2181 : RecordDataValid section14Catalog 12 (⟨319,(13),[8,12],[10],1240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1240,[3,5,7,8,9,11,12,15],1244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2182 : RecordDataValid section14Catalog 12 (⟨319,(14),[8,12],[10],1508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1508,[5,8,9,12],1513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2183 : RecordDataValid section14Catalog 12 (⟨319,(15),[8,12],[10],1508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1508,[5,8,9,12],1513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2184 : RecordDataValid section14Catalog 12 (⟨319,(16),[8,12],[10],1242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1242,[3,5,7,8,9,11,12,15],1246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2185 : RecordDataValid section14Catalog 12 (⟨319,(17),[8,12],[10],1243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1243,[3,5,7,8,9,11,12,15],1247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2186 : RecordDataValid section14Catalog 12 (⟨319,(18),[8,12],[10],1509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1509,[5,8,9,12],1514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2187 : RecordDataValid section14Catalog 12 (⟨319,(19),[8,12],[10],1509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1509,[5,8,9,12],1514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2188 : RecordDataValid section14Catalog 12 (⟨321,(0),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2189 : RecordDataValid section14Catalog 12 (⟨321,(1),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2190 : RecordDataValid section14Catalog 12 (⟨321,(2),[8,12],[10],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2191 : RecordDataValid section14Catalog 12 (⟨321,(3),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2192 : RecordDataValid section14Catalog 12 (⟨321,(4),[8,12],[10],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2193 : RecordDataValid section14Catalog 12 (⟨321,(5),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2194 : RecordDataValid section14Catalog 12 (⟨321,(6),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2195 : RecordDataValid section14Catalog 12 (⟨321,(7),[8,12],[10],1510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1510,[5,8,9,12],1515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2196 : RecordDataValid section14Catalog 12 (⟨321,(8),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2197 : RecordDataValid section14Catalog 12 (⟨321,(9),[8,12],[10],1510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1510,[5,8,9,12],1515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2198 : RecordDataValid section14Catalog 12 (⟨321,(10),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2199 : RecordDataValid section14Catalog 12 (⟨321,(11),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2200 : RecordDataValid section14Catalog 12 (⟨321,(12),[8,12],[10],1511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1511,[5,8,9,12],1516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2201 : RecordDataValid section14Catalog 12 (⟨321,(13),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2202 : RecordDataValid section14Catalog 12 (⟨321,(14),[8,12],[10],1511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1511,[5,8,9,12],1516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2203 : RecordDataValid section14Catalog 12 (⟨321,(15),[8,12],[10],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2204 : RecordDataValid section14Catalog 12 (⟨321,(16),[8,12],[10],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2205 : RecordDataValid section14Catalog 12 (⟨321,(17),[8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2206 : RecordDataValid section14Catalog 12 (⟨321,(18),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2207 : RecordDataValid section14Catalog 12 (⟨321,(19),[8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2176).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2176).take 32 = [⟨319,(8),[8,12],[10],1235⟩,⟨319,(9),[8,12],[10],1236⟩,⟨319,(10),[8,12],[10],1506⟩,⟨319,(11),[8,12],[10],1507⟩,⟨319,(12),[8,12],[10],1239⟩,⟨319,(13),[8,12],[10],1240⟩,⟨319,(14),[8,12],[10],1508⟩,⟨319,(15),[8,12],[10],1508⟩,⟨319,(16),[8,12],[10],1242⟩,⟨319,(17),[8,12],[10],1243⟩,⟨319,(18),[8,12],[10],1509⟩,⟨319,(19),[8,12],[10],1509⟩,⟨321,(0),[8,12],[10],882⟩,⟨321,(1),[8,12],[10],1497⟩,⟨321,(2),[8,12],[10],1245⟩,⟨321,(3),[8,12],[10],101⟩,⟨321,(4),[8,12],[10],1245⟩,⟨321,(5),[8,12],[10],882⟩,⟨321,(6),[8,12],[10],1497⟩,⟨321,(7),[8,12],[10],1510⟩,⟨321,(8),[8,12],[10],101⟩,⟨321,(9),[8,12],[10],1510⟩,⟨321,(10),[8,12],[10],882⟩,⟨321,(11),[8,12],[10],1497⟩,⟨321,(12),[8,12],[10],1511⟩,⟨321,(13),[8,12],[10],101⟩,⟨321,(14),[8,12],[10],1511⟩,⟨321,(15),[8,12],[10],625⟩,⟨321,(16),[8,12],[10],626⟩,⟨321,(17),[8,12],[10],286⟩,⟨321,(18),[8,12],[10],101⟩,⟨321,(19),[8,12],[10],286⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2176
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2177
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2178
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2179
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2180
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2181
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2182
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2183
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2184
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2185
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2186
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2187
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2188
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2189
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2190
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2191
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2192
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2193
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2194
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2195
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2196
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2197
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2198
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2199
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2200
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2201
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2202
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2203
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2204
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2205
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2206
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2207
end Section14Records_12_2176_2208

#print axioms solution
