-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_2176_2304
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:11:29.238412+00:00
-- url     : https://prove2.me/submissions/1e9c4ad0-dfb6-4f8d-a501-7948843bdfef

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2176_2208
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2176_2208
private theorem valid2176 : RecordDataValid section14Catalog 5 (⟨119,(22),[1,5,6,13],[170],478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨478,[1,4,5,6,8,9,10,12,13,16],479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2177 : RecordDataValid section14Catalog 5 (⟨119,(23),[1,5,6,13],[170],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2178 : RecordDataValid section14Catalog 5 (⟨119,(24),[1,5,6,13],[170],479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨479,[1,4,5,6,8,9,10,12,13,16],480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2179 : RecordDataValid section14Catalog 5 (⟨121,(0),[1,5,6,13],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2180 : RecordDataValid section14Catalog 5 (⟨121,(1),[1,5,6,13],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2181 : RecordDataValid section14Catalog 5 (⟨121,(2),[1,5,6,13],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2182 : RecordDataValid section14Catalog 5 (⟨121,(3),[1,5,6,13],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2183 : RecordDataValid section14Catalog 5 (⟨121,(4),[1,5,6,13],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2184 : RecordDataValid section14Catalog 5 (⟨121,(5),[1,5,6,13],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2185 : RecordDataValid section14Catalog 5 (⟨121,(6),[1,5,6,13],[170],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2186 : RecordDataValid section14Catalog 5 (⟨121,(7),[1,5,6,13],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2187 : RecordDataValid section14Catalog 5 (⟨121,(8),[1,5,6,13],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2188 : RecordDataValid section14Catalog 5 (⟨121,(9),[1,5,6,13],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2189 : RecordDataValid section14Catalog 5 (⟨121,(10),[1,5,6,13],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2190 : RecordDataValid section14Catalog 5 (⟨121,(11),[1,5,6,13],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2191 : RecordDataValid section14Catalog 5 (⟨121,(12),[1,5,6,13],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2192 : RecordDataValid section14Catalog 5 (⟨121,(13),[1,5,6,13],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2193 : RecordDataValid section14Catalog 5 (⟨121,(14),[1,5,6,13],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2194 : RecordDataValid section14Catalog 5 (⟨121,(15),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2195 : RecordDataValid section14Catalog 5 (⟨121,(16),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2196 : RecordDataValid section14Catalog 5 (⟨121,(17),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2197 : RecordDataValid section14Catalog 5 (⟨121,(18),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2198 : RecordDataValid section14Catalog 5 (⟨121,(19),[1,5,6,13],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2199 : RecordDataValid section14Catalog 5 (⟨121,(20),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2200 : RecordDataValid section14Catalog 5 (⟨121,(21),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2201 : RecordDataValid section14Catalog 5 (⟨121,(22),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2202 : RecordDataValid section14Catalog 5 (⟨121,(23),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2203 : RecordDataValid section14Catalog 5 (⟨121,(24),[1,5,6,13],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2204 : RecordDataValid section14Catalog 5 (⟨124,(0),[1,5,6,13],[170],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2205 : RecordDataValid section14Catalog 5 (⟨124,(1),[1,5,6,13],[170],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2206 : RecordDataValid section14Catalog 5 (⟨124,(2),[1,5,6,13],[170],490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨490,[1,4,5,6,8,9,10,12,13,16],491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2207 : RecordDataValid section14Catalog 5 (⟨124,(3),[1,5,6,13],[170],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2176_2208 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2176).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2176).take 32 = [⟨119,(22),[1,5,6,13],[170],478⟩,⟨119,(23),[1,5,6,13],[170],477⟩,⟨119,(24),[1,5,6,13],[170],479⟩,⟨121,(0),[1,5,6,13],[170],481⟩,⟨121,(1),[1,5,6,13],[170],482⟩,⟨121,(2),[1,5,6,13],[170],481⟩,⟨121,(3),[1,5,6,13],[170],483⟩,⟨121,(4),[1,5,6,13],[170],484⟩,⟨121,(5),[1,5,6,13],[170],481⟩,⟨121,(6),[1,5,6,13],[170],482⟩,⟨121,(7),[1,5,6,13],[170],481⟩,⟨121,(8),[1,5,6,13],[170],483⟩,⟨121,(9),[1,5,6,13],[170],484⟩,⟨121,(10),[1,5,6,13],[170],485⟩,⟨121,(11),[1,5,6,13],[170],485⟩,⟨121,(12),[1,5,6,13],[170],485⟩,⟨121,(13),[1,5,6,13],[170],485⟩,⟨121,(14),[1,5,6,13],[170],484⟩,⟨121,(15),[1,5,6,13],[170],486⟩,⟨121,(16),[1,5,6,13],[170],486⟩,⟨121,(17),[1,5,6,13],[170],486⟩,⟨121,(18),[1,5,6,13],[170],486⟩,⟨121,(19),[1,5,6,13],[170],486⟩,⟨121,(20),[1,5,6,13],[170],487⟩,⟨121,(21),[1,5,6,13],[170],487⟩,⟨121,(22),[1,5,6,13],[170],487⟩,⟨121,(23),[1,5,6,13],[170],487⟩,⟨121,(24),[1,5,6,13],[170],487⟩,⟨124,(0),[1,5,6,13],[170],488⟩,⟨124,(1),[1,5,6,13],[170],489⟩,⟨124,(2),[1,5,6,13],[170],490⟩,⟨124,(3),[1,5,6,13],[170],491⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2176
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2177
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2178
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2179
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2180
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2181
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2182
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2183
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2184
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2185
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2186
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2187
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2188
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2189
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2190
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2191
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2192
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2193
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2194
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2195
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2196
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2197
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2198
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2199
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2200
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2201
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2202
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2203
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2204
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2205
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2206
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2207
end Section14Records_5_2176_2208

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2176_2208


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2208_2240
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2208_2240
private theorem valid2208 : RecordDataValid section14Catalog 5 (⟨124,(4),[1,5,6,13],[170],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2209 : RecordDataValid section14Catalog 5 (⟨124,(5),[1,5,6,13],[170],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2210 : RecordDataValid section14Catalog 5 (⟨124,(6),[1,5,6,13],[170],492⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨492,[1,4,5,6,8,9,10,12,13,16],493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2211 : RecordDataValid section14Catalog 5 (⟨124,(7),[1,5,6,13],[170],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2212 : RecordDataValid section14Catalog 5 (⟨124,(8),[1,5,6,13],[170],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2213 : RecordDataValid section14Catalog 5 (⟨124,(9),[1,5,6,13],[170],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2214 : RecordDataValid section14Catalog 5 (⟨124,(10),[1,5,6,13],[170],490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨490,[1,4,5,6,8,9,10,12,13,16],491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2215 : RecordDataValid section14Catalog 5 (⟨124,(11),[1,5,6,13],[170],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2216 : RecordDataValid section14Catalog 5 (⟨124,(12),[1,5,6,13],[170],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2217 : RecordDataValid section14Catalog 5 (⟨124,(13),[1,5,6,13],[170],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2218 : RecordDataValid section14Catalog 5 (⟨124,(14),[1,5,6,13],[170],493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨493,[1,4,5,6,8,9,10,12,13,16],494⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2219 : RecordDataValid section14Catalog 5 (⟨124,(15),[1,5,6,13],[170],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2220 : RecordDataValid section14Catalog 5 (⟨127,(0),[1,5,6,13],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2221 : RecordDataValid section14Catalog 5 (⟨127,(1),[1,5,6,13],[170],495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨495,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2222 : RecordDataValid section14Catalog 5 (⟨127,(2),[1,5,6,13],[170],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2223 : RecordDataValid section14Catalog 5 (⟨127,(3),[1,5,6,13],[170],496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨496,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2224 : RecordDataValid section14Catalog 5 (⟨127,(4),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2225 : RecordDataValid section14Catalog 5 (⟨127,(5),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2226 : RecordDataValid section14Catalog 5 (⟨127,(6),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2227 : RecordDataValid section14Catalog 5 (⟨127,(7),[1,5,6,13],[170],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2228 : RecordDataValid section14Catalog 5 (⟨127,(8),[1,5,6,13],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2229 : RecordDataValid section14Catalog 5 (⟨127,(9),[1,5,6,13],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2230 : RecordDataValid section14Catalog 5 (⟨127,(10),[1,5,6,13],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2231 : RecordDataValid section14Catalog 5 (⟨127,(11),[1,5,6,13],[170],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2232 : RecordDataValid section14Catalog 5 (⟨127,(12),[1,5,6,13],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2233 : RecordDataValid section14Catalog 5 (⟨127,(13),[1,5,6,13],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2234 : RecordDataValid section14Catalog 5 (⟨127,(14),[1,5,6,13],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2235 : RecordDataValid section14Catalog 5 (⟨127,(15),[1,5,6,13],[170],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2236 : RecordDataValid section14Catalog 5 (⟨129,(0),[1,5,6],[170],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2237 : RecordDataValid section14Catalog 5 (⟨129,(1),[1,5,6],[170],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2238 : RecordDataValid section14Catalog 5 (⟨129,(2),[1,5,6],[170],502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨502,[1,4,5,6,8,9,10,12],503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2239 : RecordDataValid section14Catalog 5 (⟨129,(3),[1,5,6],[170],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2208_2240 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2208).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2208).take 32 = [⟨124,(4),[1,5,6,13],[170],488⟩,⟨124,(5),[1,5,6,13],[170],489⟩,⟨124,(6),[1,5,6,13],[170],492⟩,⟨124,(7),[1,5,6,13],[170],491⟩,⟨124,(8),[1,5,6,13],[170],488⟩,⟨124,(9),[1,5,6,13],[170],489⟩,⟨124,(10),[1,5,6,13],[170],490⟩,⟨124,(11),[1,5,6,13],[170],491⟩,⟨124,(12),[1,5,6,13],[170],488⟩,⟨124,(13),[1,5,6,13],[170],489⟩,⟨124,(14),[1,5,6,13],[170],493⟩,⟨124,(15),[1,5,6,13],[170],491⟩,⟨127,(0),[1,5,6,13],[170],494⟩,⟨127,(1),[1,5,6,13],[170],495⟩,⟨127,(2),[1,5,6,13],[170],494⟩,⟨127,(3),[1,5,6,13],[170],496⟩,⟨127,(4),[1,5,6,13],[170],497⟩,⟨127,(5),[1,5,6,13],[170],497⟩,⟨127,(6),[1,5,6,13],[170],497⟩,⟨127,(7),[1,5,6,13],[170],497⟩,⟨127,(8),[1,5,6,13],[170],498⟩,⟨127,(9),[1,5,6,13],[170],498⟩,⟨127,(10),[1,5,6,13],[170],498⟩,⟨127,(11),[1,5,6,13],[170],498⟩,⟨127,(12),[1,5,6,13],[170],499⟩,⟨127,(13),[1,5,6,13],[170],499⟩,⟨127,(14),[1,5,6,13],[170],499⟩,⟨127,(15),[1,5,6,13],[170],499⟩,⟨129,(0),[1,5,6],[170],500⟩,⟨129,(1),[1,5,6],[170],501⟩,⟨129,(2),[1,5,6],[170],502⟩,⟨129,(3),[1,5,6],[170],503⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2208
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2209
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2210
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2211
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2212
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2213
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2214
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2215
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2216
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2217
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2218
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2219
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2220
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2221
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2222
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2223
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2224
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2225
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2226
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2227
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2228
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2229
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2230
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2231
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2232
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2233
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2234
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2235
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2236
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2237
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2238
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2239
end Section14Records_5_2208_2240

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2208_2240


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2240_2272
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2240_2272
private theorem valid2240 : RecordDataValid section14Catalog 5 (⟨129,(4),[1,5,6],[170],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2241 : RecordDataValid section14Catalog 5 (⟨129,(5),[1,5,6],[170],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2242 : RecordDataValid section14Catalog 5 (⟨129,(6),[1,5,6],[170],504⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨504,[1,4,5,6,8,9,10,12],505⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2243 : RecordDataValid section14Catalog 5 (⟨129,(7),[1,5,6],[170],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2244 : RecordDataValid section14Catalog 5 (⟨129,(8),[1,5,6],[170],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2245 : RecordDataValid section14Catalog 5 (⟨129,(9),[1,5,6],[170],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2246 : RecordDataValid section14Catalog 5 (⟨129,(10),[1,5,6],[170],502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨502,[1,4,5,6,8,9,10,12],503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2247 : RecordDataValid section14Catalog 5 (⟨129,(11),[1,5,6],[170],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2248 : RecordDataValid section14Catalog 5 (⟨129,(12),[1,5,6],[170],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2249 : RecordDataValid section14Catalog 5 (⟨129,(13),[1,5,6],[170],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2250 : RecordDataValid section14Catalog 5 (⟨129,(14),[1,5,6],[170],505⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨505,[1,4,5,6,8,9,10,12],506⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2251 : RecordDataValid section14Catalog 5 (⟨129,(15),[1,5,6],[170],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2252 : RecordDataValid section14Catalog 5 (⟨132,(0),[1,5,6],[170],506⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨506,[1,2,3,4,5,6,7,8,9,10,11,12],507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2253 : RecordDataValid section14Catalog 5 (⟨132,(1),[1,5,6],[170],507⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨507,[1,2,3,4,5,6,7,8,9,10,11,12],508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2254 : RecordDataValid section14Catalog 5 (⟨132,(2),[1,5,6],[170],508⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨508,[1,2,3,4,5,6,7,8,9,10,11,12],509⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2255 : RecordDataValid section14Catalog 5 (⟨132,(3),[1,5,6],[170],509⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨509,[1,2,3,4,5,6,7,8,9,10,11,12],510⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2256 : RecordDataValid section14Catalog 5 (⟨134,(0),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2257 : RecordDataValid section14Catalog 5 (⟨134,(1),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2258 : RecordDataValid section14Catalog 5 (⟨134,(2),[1,5,6,13],[170],510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨510,[1,5,6,9,10,13],511⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2259 : RecordDataValid section14Catalog 5 (⟨134,(3),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2260 : RecordDataValid section14Catalog 5 (⟨134,(4),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2261 : RecordDataValid section14Catalog 5 (⟨134,(5),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2262 : RecordDataValid section14Catalog 5 (⟨134,(6),[1,5,6,13],[170],511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨511,[1,2,5,6,9,10,13,14],512⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2263 : RecordDataValid section14Catalog 5 (⟨134,(7),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2264 : RecordDataValid section14Catalog 5 (⟨134,(8),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2265 : RecordDataValid section14Catalog 5 (⟨134,(9),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2266 : RecordDataValid section14Catalog 5 (⟨134,(10),[1,5,6,13],[170],512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨512,[1,2,4,5,6,8,9,10,12,13,14,16],513⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2267 : RecordDataValid section14Catalog 5 (⟨134,(11),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2268 : RecordDataValid section14Catalog 5 (⟨134,(12),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2269 : RecordDataValid section14Catalog 5 (⟨134,(13),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2270 : RecordDataValid section14Catalog 5 (⟨134,(14),[1,5,6,13],[170],513⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨513,[1,2,5,6,9,10,13,14],514⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2271 : RecordDataValid section14Catalog 5 (⟨134,(15),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2240_2272 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2240).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2240).take 32 = [⟨129,(4),[1,5,6],[170],500⟩,⟨129,(5),[1,5,6],[170],501⟩,⟨129,(6),[1,5,6],[170],504⟩,⟨129,(7),[1,5,6],[170],503⟩,⟨129,(8),[1,5,6],[170],500⟩,⟨129,(9),[1,5,6],[170],501⟩,⟨129,(10),[1,5,6],[170],502⟩,⟨129,(11),[1,5,6],[170],503⟩,⟨129,(12),[1,5,6],[170],500⟩,⟨129,(13),[1,5,6],[170],501⟩,⟨129,(14),[1,5,6],[170],505⟩,⟨129,(15),[1,5,6],[170],503⟩,⟨132,(0),[1,5,6],[170],506⟩,⟨132,(1),[1,5,6],[170],507⟩,⟨132,(2),[1,5,6],[170],508⟩,⟨132,(3),[1,5,6],[170],509⟩,⟨134,(0),[1,5,6,13],[170],3⟩,⟨134,(1),[1,5,6,13],[170],3⟩,⟨134,(2),[1,5,6,13],[170],510⟩,⟨134,(3),[1,5,6,13],[170],29⟩,⟨134,(4),[1,5,6,13],[170],3⟩,⟨134,(5),[1,5,6,13],[170],3⟩,⟨134,(6),[1,5,6,13],[170],511⟩,⟨134,(7),[1,5,6,13],[170],29⟩,⟨134,(8),[1,5,6,13],[170],3⟩,⟨134,(9),[1,5,6,13],[170],3⟩,⟨134,(10),[1,5,6,13],[170],512⟩,⟨134,(11),[1,5,6,13],[170],29⟩,⟨134,(12),[1,5,6,13],[170],3⟩,⟨134,(13),[1,5,6,13],[170],3⟩,⟨134,(14),[1,5,6,13],[170],513⟩,⟨134,(15),[1,5,6,13],[170],29⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2240
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2241
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2242
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2243
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2244
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2245
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2246
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2247
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2248
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2249
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2250
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2251
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2252
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2253
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2254
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2255
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2256
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2257
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2258
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2259
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2260
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2261
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2262
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2263
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2264
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2265
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2266
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2267
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2268
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2269
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2270
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2271
end Section14Records_5_2240_2272

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2240_2272


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2272_2304
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_2272_2304
private theorem valid2272 : RecordDataValid section14Catalog 5 (⟨134,(16),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2273 : RecordDataValid section14Catalog 5 (⟨134,(17),[1,5,6,13],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2274 : RecordDataValid section14Catalog 5 (⟨134,(18),[1,5,6,13],[170],514⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨514,[1,2,4,5,6,8,9,10,12,13,14,16],515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2275 : RecordDataValid section14Catalog 5 (⟨134,(19),[1,5,6,13],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2276 : RecordDataValid section14Catalog 5 (⟨135,(0),[1,5,6,13],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2277 : RecordDataValid section14Catalog 5 (⟨135,(1),[1,5,6,13],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2278 : RecordDataValid section14Catalog 5 (⟨135,(2),[1,5,6,13],[170],516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨516,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2279 : RecordDataValid section14Catalog 5 (⟨135,(3),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2280 : RecordDataValid section14Catalog 5 (⟨135,(4),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2281 : RecordDataValid section14Catalog 5 (⟨135,(5),[1,5,6,13],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2282 : RecordDataValid section14Catalog 5 (⟨135,(6),[1,5,6,13],[170],515⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨515,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2283 : RecordDataValid section14Catalog 5 (⟨135,(7),[1,5,6,13],[170],516⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨516,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2284 : RecordDataValid section14Catalog 5 (⟨135,(8),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2285 : RecordDataValid section14Catalog 5 (⟨135,(9),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2286 : RecordDataValid section14Catalog 5 (⟨135,(10),[1,5,6,13],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2287 : RecordDataValid section14Catalog 5 (⟨135,(11),[1,5,6,13],[170],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2288 : RecordDataValid section14Catalog 5 (⟨135,(12),[1,5,6,13],[170],520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨520,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],521⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2289 : RecordDataValid section14Catalog 5 (⟨135,(13),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2290 : RecordDataValid section14Catalog 5 (⟨135,(14),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2291 : RecordDataValid section14Catalog 5 (⟨135,(15),[1,5,6,13],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2292 : RecordDataValid section14Catalog 5 (⟨135,(16),[1,5,6,13],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2293 : RecordDataValid section14Catalog 5 (⟨135,(17),[1,5,6,13],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2294 : RecordDataValid section14Catalog 5 (⟨135,(18),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2295 : RecordDataValid section14Catalog 5 (⟨135,(19),[1,5,6,13],[170],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2296 : RecordDataValid section14Catalog 5 (⟨135,(20),[1,5,6,13],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2297 : RecordDataValid section14Catalog 5 (⟨135,(21),[1,5,6,13],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2298 : RecordDataValid section14Catalog 5 (⟨135,(22),[1,5,6,13],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2299 : RecordDataValid section14Catalog 5 (⟨135,(23),[1,5,6,13],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2300 : RecordDataValid section14Catalog 5 (⟨135,(24),[1,5,6,13],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2301 : RecordDataValid section14Catalog 5 (⟨136,(0),[5],[170],524⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨524,[1,4,5,6,8,9,10,12,13,16],525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2302 : RecordDataValid section14Catalog 5 (⟨136,(1),[1,5,6,13],[170],524⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨524,[1,4,5,6,8,9,10,12,13,16],525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2303 : RecordDataValid section14Catalog 5 (⟨136,(2),[1,5,6,13],[170],524⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨524,[1,4,5,6,8,9,10,12,13,16],525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_2272_2304 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2272).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2272).take 32 = [⟨134,(16),[1,5,6,13],[170],3⟩,⟨134,(17),[1,5,6,13],[170],3⟩,⟨134,(18),[1,5,6,13],[170],514⟩,⟨134,(19),[1,5,6,13],[170],29⟩,⟨135,(0),[1,5,6,13],[170],515⟩,⟨135,(1),[1,5,6,13],[170],515⟩,⟨135,(2),[1,5,6,13],[170],516⟩,⟨135,(3),[1,5,6,13],[170],517⟩,⟨135,(4),[1,5,6,13],[170],518⟩,⟨135,(5),[1,5,6,13],[170],515⟩,⟨135,(6),[1,5,6,13],[170],515⟩,⟨135,(7),[1,5,6,13],[170],516⟩,⟨135,(8),[1,5,6,13],[170],517⟩,⟨135,(9),[1,5,6,13],[170],518⟩,⟨135,(10),[1,5,6,13],[170],519⟩,⟨135,(11),[1,5,6,13],[170],519⟩,⟨135,(12),[1,5,6,13],[170],520⟩,⟨135,(13),[1,5,6,13],[170],517⟩,⟨135,(14),[1,5,6,13],[170],518⟩,⟨135,(15),[1,5,6,13],[170],521⟩,⟨135,(16),[1,5,6,13],[170],521⟩,⟨135,(17),[1,5,6,13],[170],521⟩,⟨135,(18),[1,5,6,13],[170],517⟩,⟨135,(19),[1,5,6,13],[170],521⟩,⟨135,(20),[1,5,6,13],[170],522⟩,⟨135,(21),[1,5,6,13],[170],522⟩,⟨135,(22),[1,5,6,13],[170],522⟩,⟨135,(23),[1,5,6,13],[170],517⟩,⟨135,(24),[1,5,6,13],[170],518⟩,⟨136,(0),[5],[170],524⟩,⟨136,(1),[1,5,6,13],[170],524⟩,⟨136,(2),[1,5,6,13],[170],524⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2272
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2273
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2274
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2275
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2276
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2277
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2278
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2279
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2280
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2281
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2282
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2283
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2284
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2285
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2286
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2287
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2288
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2289
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2290
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2291
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2292
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2293
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2294
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2295
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2296
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2297
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2298
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2299
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2300
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2301
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2302
  · exact recordValid_of_data section14Catalog 5 _ hnum valid2303
end Section14Records_5_2272_2304

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_2272_2304

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 2176).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 2176 2240 2304 (by decide) (by decide) (all_of_interval_split P xs 2176 2208 2240 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_2176_2208 hnum) (Freiman.workReverse20260919_s0005_records_2208_2240 hnum)) (all_of_interval_split P xs 2240 2272 2304 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_2240_2272 hnum) (Freiman.workReverse20260919_s0005_records_2272_2304 hnum)))

#print axioms solution
