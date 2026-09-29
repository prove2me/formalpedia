-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_1152_1408
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:04:29.336853+00:00
-- url     : https://prove2.me/submissions/149cb5de-d776-4e06-aaf2-4d9d4871c154

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1152_1184
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1152_1184
private theorem valid1152 : RecordDataValid section14Catalog 1 (⟨28,(24),[1,2],[190],228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨228,[1,2],228⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1153 : RecordDataValid section14Catalog 1 (⟨28,(24),[1,2,5,6],[131],118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨118,[1,2,5,6,9,10],118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1154 : RecordDataValid section14Catalog 1 (⟨28,(24),[1,2,5,6],[150],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1155 : RecordDataValid section14Catalog 1 (⟨28,(24),[1,5],[130],90⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨90,[1,5,9],90⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1156 : RecordDataValid section14Catalog 1 (⟨28,(24),[1,5],[134,135],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1157 : RecordDataValid section14Catalog 1 (⟨30,(0),[1],[134],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1158 : RecordDataValid section14Catalog 1 (⟨30,(0),[1],[135,151],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1159 : RecordDataValid section14Catalog 1 (⟨30,(0),[1,2],[130],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1160 : RecordDataValid section14Catalog 1 (⟨30,(0),[1,2],[147],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1161 : RecordDataValid section14Catalog 1 (⟨30,(0),[1,2],[190],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1162 : RecordDataValid section14Catalog 1 (⟨30,(0),[1,2,5,6],[146,150],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1163 : RecordDataValid section14Catalog 1 (⟨30,(0),[1,6],[131],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1164 : RecordDataValid section14Catalog 1 (⟨30,(1),[1],[134,135],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1165 : RecordDataValid section14Catalog 1 (⟨30,(1),[1],[151],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1166 : RecordDataValid section14Catalog 1 (⟨30,(1),[1,2],[130,131],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1167 : RecordDataValid section14Catalog 1 (⟨30,(1),[1,2],[190],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1168 : RecordDataValid section14Catalog 1 (⟨30,(1),[1,2],[147],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1169 : RecordDataValid section14Catalog 1 (⟨30,(1),[1,2,5,6],[146,150],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1170 : RecordDataValid section14Catalog 1 (⟨30,(2),[1],[151],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1171 : RecordDataValid section14Catalog 1 (⟨30,(2),[1,2],[147],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1172 : RecordDataValid section14Catalog 1 (⟨30,(2),[1,2],[190],200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨200,[1,2,3,4,5,6,7,8,9,10,11,12],200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1173 : RecordDataValid section14Catalog 1 (⟨30,(2),[1,2,5,6],[130],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1174 : RecordDataValid section14Catalog 1 (⟨30,(2),[1,2,5,6],[146],154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨154,[1,2,3,5,6,7],154⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1175 : RecordDataValid section14Catalog 1 (⟨30,(2),[1,2,5,6],[150],200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨200,[1,2,3,4,5,6,7,8,9,10,11,12],200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1176 : RecordDataValid section14Catalog 1 (⟨30,(2),[1,5],[134],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1177 : RecordDataValid section14Catalog 1 (⟨30,(2),[1,5],[135],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1178 : RecordDataValid section14Catalog 1 (⟨30,(2),[1,5,6],[131],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1179 : RecordDataValid section14Catalog 1 (⟨30,(3),[1],[135],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1180 : RecordDataValid section14Catalog 1 (⟨30,(3),[1],[151],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1181 : RecordDataValid section14Catalog 1 (⟨30,(3),[1,2],[131],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1182 : RecordDataValid section14Catalog 1 (⟨30,(3),[1,2],[147],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1183 : RecordDataValid section14Catalog 1 (⟨30,(3),[1,2],[150],201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨201,[1,2,3,4],201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1152_1184 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1152).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1152).take 32 = [⟨28,(24),[1,2],[190],228⟩,⟨28,(24),[1,2,5,6],[131],118⟩,⟨28,(24),[1,2,5,6],[150],137⟩,⟨28,(24),[1,5],[130],90⟩,⟨28,(24),[1,5],[134,135],137⟩,⟨30,(0),[1],[134],92⟩,⟨30,(0),[1],[135,151],120⟩,⟨30,(0),[1,2],[130],92⟩,⟨30,(0),[1,2],[147],120⟩,⟨30,(0),[1,2],[190],152⟩,⟨30,(0),[1,2,5,6],[146,150],152⟩,⟨30,(0),[1,6],[131],120⟩,⟨30,(1),[1],[134,135],93⟩,⟨30,(1),[1],[151],181⟩,⟨30,(1),[1,2],[130,131],93⟩,⟨30,(1),[1,2],[190],153⟩,⟨30,(1),[1,2],[147],181⟩,⟨30,(1),[1,2,5,6],[146,150],153⟩,⟨30,(2),[1],[151],120⟩,⟨30,(2),[1,2],[147],120⟩,⟨30,(2),[1,2],[190],200⟩,⟨30,(2),[1,2,5,6],[130],92⟩,⟨30,(2),[1,2,5,6],[146],154⟩,⟨30,(2),[1,2,5,6],[150],200⟩,⟨30,(2),[1,5],[134],92⟩,⟨30,(2),[1,5],[135],120⟩,⟨30,(2),[1,5,6],[131],120⟩,⟨30,(3),[1],[135],93⟩,⟨30,(3),[1],[151],181⟩,⟨30,(3),[1,2],[131],93⟩,⟨30,(3),[1,2],[147],181⟩,⟨30,(3),[1,2],[150],201⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1152
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1153
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1154
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1155
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1156
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1157
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1158
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1159
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1160
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1161
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1162
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1163
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1164
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1165
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1166
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1167
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1168
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1169
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1170
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1171
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1172
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1173
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1174
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1175
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1176
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1177
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1178
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1179
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1180
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1181
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1182
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1183
end Section14Records_1_1152_1184

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1152_1184


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1184_1216
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1184_1216
private theorem valid1184 : RecordDataValid section14Catalog 1 (⟨30,(3),[1,2],[190],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1185 : RecordDataValid section14Catalog 1 (⟨30,(3),[1,2,5,6],[130],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1186 : RecordDataValid section14Catalog 1 (⟨30,(3),[1,2,5,6],[146],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1187 : RecordDataValid section14Catalog 1 (⟨30,(3),[1,5],[134],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1188 : RecordDataValid section14Catalog 1 (⟨30,(4),[1],[135],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1189 : RecordDataValid section14Catalog 1 (⟨30,(4),[1],[151],182⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨182,[1,2,5,6,9,10],182⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1190 : RecordDataValid section14Catalog 1 (⟨30,(4),[1,2],[131],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1191 : RecordDataValid section14Catalog 1 (⟨30,(4),[1,2],[147],182⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨182,[1,2,5,6,9,10],182⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1192 : RecordDataValid section14Catalog 1 (⟨30,(4),[1,2],[150],202⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨202,[1,2,3,4],202⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1193 : RecordDataValid section14Catalog 1 (⟨30,(4),[1,2],[190],231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨231,[1,2,3,4,5,6,7,8,9,10,11,12],231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1194 : RecordDataValid section14Catalog 1 (⟨30,(4),[1,2,5,6],[130],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1195 : RecordDataValid section14Catalog 1 (⟨30,(4),[1,2,5,6],[146],156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨156,[1,2,3,5,6,7],156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1196 : RecordDataValid section14Catalog 1 (⟨30,(4),[1,5],[134],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1197 : RecordDataValid section14Catalog 1 (⟨30,(5),[1],[135],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1198 : RecordDataValid section14Catalog 1 (⟨30,(5),[1],[151],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1199 : RecordDataValid section14Catalog 1 (⟨30,(5),[1,2],[131],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1200 : RecordDataValid section14Catalog 1 (⟨30,(5),[1,2],[147],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1201 : RecordDataValid section14Catalog 1 (⟨30,(5),[1,2],[150],201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨201,[1,2,3,4],201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1202 : RecordDataValid section14Catalog 1 (⟨30,(5),[1,2],[190],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1203 : RecordDataValid section14Catalog 1 (⟨30,(5),[1,2,5,6],[130],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1204 : RecordDataValid section14Catalog 1 (⟨30,(5),[1,2,5,6],[146],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1205 : RecordDataValid section14Catalog 1 (⟨30,(5),[1,5],[134],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1206 : RecordDataValid section14Catalog 1 (⟨30,(6),[1],[135],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1207 : RecordDataValid section14Catalog 1 (⟨30,(6),[1],[151],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1208 : RecordDataValid section14Catalog 1 (⟨30,(6),[1,2],[131],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1209 : RecordDataValid section14Catalog 1 (⟨30,(6),[1,2],[147],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1210 : RecordDataValid section14Catalog 1 (⟨30,(6),[1,2],[150],203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨203,[1,2,3,4],203⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1211 : RecordDataValid section14Catalog 1 (⟨30,(6),[1,2],[190],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1212 : RecordDataValid section14Catalog 1 (⟨30,(6),[1,2,5,6],[130],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1213 : RecordDataValid section14Catalog 1 (⟨30,(6),[1,2,5,6],[146],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1214 : RecordDataValid section14Catalog 1 (⟨30,(6),[1,5],[134],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1215 : RecordDataValid section14Catalog 1 (⟨30,(7),[1],[135],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1184_1216 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1184).take 32 = [⟨30,(3),[1,2],[190],230⟩,⟨30,(3),[1,2,5,6],[130],93⟩,⟨30,(3),[1,2,5,6],[146],155⟩,⟨30,(3),[1,5],[134],93⟩,⟨30,(4),[1],[135],94⟩,⟨30,(4),[1],[151],182⟩,⟨30,(4),[1,2],[131],94⟩,⟨30,(4),[1,2],[147],182⟩,⟨30,(4),[1,2],[150],202⟩,⟨30,(4),[1,2],[190],231⟩,⟨30,(4),[1,2,5,6],[130],94⟩,⟨30,(4),[1,2,5,6],[146],156⟩,⟨30,(4),[1,5],[134],94⟩,⟨30,(5),[1],[135],93⟩,⟨30,(5),[1],[151],181⟩,⟨30,(5),[1,2],[131],93⟩,⟨30,(5),[1,2],[147],181⟩,⟨30,(5),[1,2],[150],201⟩,⟨30,(5),[1,2],[190],230⟩,⟨30,(5),[1,2,5,6],[130],93⟩,⟨30,(5),[1,2,5,6],[146],155⟩,⟨30,(5),[1,5],[134],93⟩,⟨30,(6),[1],[135],95⟩,⟨30,(6),[1],[151],183⟩,⟨30,(6),[1,2],[131],95⟩,⟨30,(6),[1,2],[147],183⟩,⟨30,(6),[1,2],[150],203⟩,⟨30,(6),[1,2],[190],232⟩,⟨30,(6),[1,2,5,6],[130],95⟩,⟨30,(6),[1,2,5,6],[146],157⟩,⟨30,(6),[1,5],[134],95⟩,⟨30,(7),[1],[135],95⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1184
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1185
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1186
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1187
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1188
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1189
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1190
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1191
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1192
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1193
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1194
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1195
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1196
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1197
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1198
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1199
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1200
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1201
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1202
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1203
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1204
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1205
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1206
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1207
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1208
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1209
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1210
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1211
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1212
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1213
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1214
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1215
end Section14Records_1_1184_1216

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1184_1216


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1216_1248
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1216_1248
private theorem valid1216 : RecordDataValid section14Catalog 1 (⟨30,(7),[1],[151],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1217 : RecordDataValid section14Catalog 1 (⟨30,(7),[1,2],[131],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1218 : RecordDataValid section14Catalog 1 (⟨30,(7),[1,2],[147],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1219 : RecordDataValid section14Catalog 1 (⟨30,(7),[1,2],[150],203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨203,[1,2,3,4],203⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1220 : RecordDataValid section14Catalog 1 (⟨30,(7),[1,2],[190],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1221 : RecordDataValid section14Catalog 1 (⟨30,(7),[1,2,5,6],[130],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1222 : RecordDataValid section14Catalog 1 (⟨30,(7),[1,2,5,6],[146],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1223 : RecordDataValid section14Catalog 1 (⟨30,(7),[1,5],[134],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1224 : RecordDataValid section14Catalog 1 (⟨30,(8),[1],[135],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1225 : RecordDataValid section14Catalog 1 (⟨30,(8),[1],[151],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1226 : RecordDataValid section14Catalog 1 (⟨30,(8),[1,2],[131],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1227 : RecordDataValid section14Catalog 1 (⟨30,(8),[1,2],[147],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1228 : RecordDataValid section14Catalog 1 (⟨30,(8),[1,2],[150],204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨204,[1,2,3,4,7],204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1229 : RecordDataValid section14Catalog 1 (⟨30,(8),[1,2],[190],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1230 : RecordDataValid section14Catalog 1 (⟨30,(8),[1,2,5,6],[130],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1231 : RecordDataValid section14Catalog 1 (⟨30,(8),[1,2,5,6],[146],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1232 : RecordDataValid section14Catalog 1 (⟨30,(8),[1,5],[134],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1233 : RecordDataValid section14Catalog 1 (⟨30,(9),[1],[135],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1234 : RecordDataValid section14Catalog 1 (⟨30,(9),[1],[151],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1235 : RecordDataValid section14Catalog 1 (⟨30,(9),[1,2],[131],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1236 : RecordDataValid section14Catalog 1 (⟨30,(9),[1,2],[147],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1237 : RecordDataValid section14Catalog 1 (⟨30,(9),[1,2],[150],204⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨204,[1,2,3,4,7],204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1238 : RecordDataValid section14Catalog 1 (⟨30,(9),[1,2],[190],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1239 : RecordDataValid section14Catalog 1 (⟨30,(9),[1,2,5,6],[130],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1240 : RecordDataValid section14Catalog 1 (⟨30,(9),[1,2,5,6],[146],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1241 : RecordDataValid section14Catalog 1 (⟨30,(9),[1,5],[134],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1242 : RecordDataValid section14Catalog 1 (⟨33,(0),[1],[147,151],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1243 : RecordDataValid section14Catalog 1 (⟨33,(0),[1,2,5,6],[130],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1244 : RecordDataValid section14Catalog 1 (⟨33,(0),[1,2,5,6,14],[131],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1245 : RecordDataValid section14Catalog 1 (⟨33,(0),[1,5],[134,135],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1246 : RecordDataValid section14Catalog 1 (⟨33,(0),[1,5,6],[146,150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1247 : RecordDataValid section14Catalog 1 (⟨33,(0),[1,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1216_1248 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1216).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1216).take 32 = [⟨30,(7),[1],[151],183⟩,⟨30,(7),[1,2],[131],95⟩,⟨30,(7),[1,2],[147],183⟩,⟨30,(7),[1,2],[150],203⟩,⟨30,(7),[1,2],[190],232⟩,⟨30,(7),[1,2,5,6],[130],95⟩,⟨30,(7),[1,2,5,6],[146],157⟩,⟨30,(7),[1,5],[134],95⟩,⟨30,(8),[1],[135],96⟩,⟨30,(8),[1],[151],184⟩,⟨30,(8),[1,2],[131],96⟩,⟨30,(8),[1,2],[147],184⟩,⟨30,(8),[1,2],[150],204⟩,⟨30,(8),[1,2],[190],233⟩,⟨30,(8),[1,2,5,6],[130],96⟩,⟨30,(8),[1,2,5,6],[146],158⟩,⟨30,(8),[1,5],[134],96⟩,⟨30,(9),[1],[135],96⟩,⟨30,(9),[1],[151],184⟩,⟨30,(9),[1,2],[131],96⟩,⟨30,(9),[1,2],[147],184⟩,⟨30,(9),[1,2],[150],204⟩,⟨30,(9),[1,2],[190],233⟩,⟨30,(9),[1,2,5,6],[130],96⟩,⟨30,(9),[1,2,5,6],[146],158⟩,⟨30,(9),[1,5],[134],96⟩,⟨33,(0),[1],[147,151],98⟩,⟨33,(0),[1,2,5,6],[130],97⟩,⟨33,(0),[1,2,5,6,14],[131],97⟩,⟨33,(0),[1,5],[134,135],97⟩,⟨33,(0),[1,5,6],[146,150],98⟩,⟨33,(0),[1,13,14],[190],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1216
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1217
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1218
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1219
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1220
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1221
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1222
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1223
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1224
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1225
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1226
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1227
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1228
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1229
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1230
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1231
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1232
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1233
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1234
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1235
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1236
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1237
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1238
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1239
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1240
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1241
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1242
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1243
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1244
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1245
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1246
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1247
end Section14Records_1_1216_1248

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1216_1248


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1248_1280
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1248_1280
private theorem valid1248 : RecordDataValid section14Catalog 1 (⟨33,(1),[1,5],[134,135],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1249 : RecordDataValid section14Catalog 1 (⟨33,(1),[1,5,6],[130,131],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1250 : RecordDataValid section14Catalog 1 (⟨33,(1),[1,13],[146,147,150,151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1251 : RecordDataValid section14Catalog 1 (⟨33,(1),[1,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1252 : RecordDataValid section14Catalog 1 (⟨33,(2),[1],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1253 : RecordDataValid section14Catalog 1 (⟨33,(2),[1,5],[130,131,134,135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1254 : RecordDataValid section14Catalog 1 (⟨33,(2),[1,5,6,13,14],[146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1255 : RecordDataValid section14Catalog 1 (⟨33,(2),[1,13],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1256 : RecordDataValid section14Catalog 1 (⟨33,(2),[1,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1257 : RecordDataValid section14Catalog 1 (⟨33,(3),[1,2,14],[190],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1258 : RecordDataValid section14Catalog 1 (⟨33,(3),[1,5],[134],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1259 : RecordDataValid section14Catalog 1 (⟨33,(3),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1260 : RecordDataValid section14Catalog 1 (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1261 : RecordDataValid section14Catalog 1 (⟨33,(3),[1,5,13],[135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1262 : RecordDataValid section14Catalog 1 (⟨33,(3),[1,13],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1263 : RecordDataValid section14Catalog 1 (⟨33,(3),[1,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1264 : RecordDataValid section14Catalog 1 (⟨33,(4),[1],[147,151],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1265 : RecordDataValid section14Catalog 1 (⟨33,(4),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1266 : RecordDataValid section14Catalog 1 (⟨33,(4),[1,2,5,6,13,14],[131],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1267 : RecordDataValid section14Catalog 1 (⟨33,(4),[1,5],[134],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1268 : RecordDataValid section14Catalog 1 (⟨33,(4),[1,5,6],[146,150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1269 : RecordDataValid section14Catalog 1 (⟨33,(4),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1270 : RecordDataValid section14Catalog 1 (⟨33,(4),[1,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1271 : RecordDataValid section14Catalog 1 (⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1272 : RecordDataValid section14Catalog 1 (⟨33,(5),[1,2,13,14],[147],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1273 : RecordDataValid section14Catalog 1 (⟨33,(5),[1,5],[134,135],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1274 : RecordDataValid section14Catalog 1 (⟨33,(5),[1,5,6],[130,131],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1275 : RecordDataValid section14Catalog 1 (⟨33,(5),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1276 : RecordDataValid section14Catalog 1 (⟨33,(5),[1,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1277 : RecordDataValid section14Catalog 1 (⟨33,(6),[1],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1278 : RecordDataValid section14Catalog 1 (⟨33,(6),[1,5],[134],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1279 : RecordDataValid section14Catalog 1 (⟨33,(6),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1248_1280 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1248).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1248).take 32 = [⟨33,(1),[1,5],[134,135],98⟩,⟨33,(1),[1,5,6],[130,131],98⟩,⟨33,(1),[1,13],[146,147,150,151],2⟩,⟨33,(1),[1,13,14],[190],3⟩,⟨33,(2),[1],[190],29⟩,⟨33,(2),[1,5],[130,131,134,135],3⟩,⟨33,(2),[1,5,6,13,14],[146,150],3⟩,⟨33,(2),[1,13],[151],3⟩,⟨33,(2),[1,13,14],[147],3⟩,⟨33,(3),[1,2,14],[190],234⟩,⟨33,(3),[1,5],[134],3⟩,⟨33,(3),[1,5,6],[130],3⟩,⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩,⟨33,(3),[1,5,13],[135],3⟩,⟨33,(3),[1,13],[151],3⟩,⟨33,(3),[1,13,14],[147],3⟩,⟨33,(4),[1],[147,151],98⟩,⟨33,(4),[1,2,5,6],[130],2⟩,⟨33,(4),[1,2,5,6,13,14],[131],2⟩,⟨33,(4),[1,5],[134],2⟩,⟨33,(4),[1,5,6],[146,150],98⟩,⟨33,(4),[1,5,13],[135],2⟩,⟨33,(4),[1,13,14],[190],3⟩,⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩,⟨33,(5),[1,2,13,14],[147],2⟩,⟨33,(5),[1,5],[134,135],98⟩,⟨33,(5),[1,5,6],[130,131],98⟩,⟨33,(5),[1,13],[151],2⟩,⟨33,(5),[1,13,14],[190],3⟩,⟨33,(6),[1],[190],29⟩,⟨33,(6),[1,5],[134],3⟩,⟨33,(6),[1,5,6],[130],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1248
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1249
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1250
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1251
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1252
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1253
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1254
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1255
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1256
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1257
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1258
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1259
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1260
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1261
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1262
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1263
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1264
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1265
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1266
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1267
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1268
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1269
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1270
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1271
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1272
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1273
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1274
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1275
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1276
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1277
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1278
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1279
end Section14Records_1_1248_1280

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1248_1280


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1280_1312
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1280_1312
private theorem valid1280 : RecordDataValid section14Catalog 1 (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1281 : RecordDataValid section14Catalog 1 (⟨33,(6),[1,5,13],[135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1282 : RecordDataValid section14Catalog 1 (⟨33,(6),[1,13],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1283 : RecordDataValid section14Catalog 1 (⟨33,(6),[1,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1284 : RecordDataValid section14Catalog 1 (⟨33,(7),[1,2,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1285 : RecordDataValid section14Catalog 1 (⟨33,(7),[1,5],[134],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1286 : RecordDataValid section14Catalog 1 (⟨33,(7),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1287 : RecordDataValid section14Catalog 1 (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1288 : RecordDataValid section14Catalog 1 (⟨33,(7),[1,5,13],[135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1289 : RecordDataValid section14Catalog 1 (⟨33,(7),[1,13],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1290 : RecordDataValid section14Catalog 1 (⟨33,(7),[1,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1291 : RecordDataValid section14Catalog 1 (⟨33,(8),[1,2,5,6],[130],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1292 : RecordDataValid section14Catalog 1 (⟨33,(8),[1,2,5,6,13,14],[131],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1293 : RecordDataValid section14Catalog 1 (⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1294 : RecordDataValid section14Catalog 1 (⟨33,(8),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1295 : RecordDataValid section14Catalog 1 (⟨33,(8),[1,2,13,14],[147],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1296 : RecordDataValid section14Catalog 1 (⟨33,(8),[1,5],[134],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1297 : RecordDataValid section14Catalog 1 (⟨33,(8),[1,5,13],[135],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1298 : RecordDataValid section14Catalog 1 (⟨33,(8),[1,13],[151],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1299 : RecordDataValid section14Catalog 1 (⟨33,(9),[1,2,5,6],[130],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1300 : RecordDataValid section14Catalog 1 (⟨33,(9),[1,2,5,6,13,14],[131],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1301 : RecordDataValid section14Catalog 1 (⟨33,(9),[1,2,5,6,13,14],[146,150],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1302 : RecordDataValid section14Catalog 1 (⟨33,(9),[1,2,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1303 : RecordDataValid section14Catalog 1 (⟨33,(9),[1,2,13,14],[147],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1304 : RecordDataValid section14Catalog 1 (⟨33,(9),[1,5],[134],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1305 : RecordDataValid section14Catalog 1 (⟨33,(9),[1,5,13],[135],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1306 : RecordDataValid section14Catalog 1 (⟨33,(9),[1,13],[151],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1307 : RecordDataValid section14Catalog 1 (⟨33,(10),[1],[134,135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1308 : RecordDataValid section14Catalog 1 (⟨33,(10),[1,2],[130,131],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1309 : RecordDataValid section14Catalog 1 (⟨33,(10),[1,2,5,6,13,14],[146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1310 : RecordDataValid section14Catalog 1 (⟨33,(10),[1,2,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1311 : RecordDataValid section14Catalog 1 (⟨33,(10),[1,2,13,14],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1280_1312 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1280).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1280).take 32 = [⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩,⟨33,(6),[1,5,13],[135],3⟩,⟨33,(6),[1,13],[151],3⟩,⟨33,(6),[1,13,14],[147],3⟩,⟨33,(7),[1,2,13,14],[190],2⟩,⟨33,(7),[1,5],[134],3⟩,⟨33,(7),[1,5,6],[130],3⟩,⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩,⟨33,(7),[1,5,13],[135],3⟩,⟨33,(7),[1,13],[151],3⟩,⟨33,(7),[1,13,14],[147],3⟩,⟨33,(8),[1,2,5,6],[130],97⟩,⟨33,(8),[1,2,5,6,13,14],[131],97⟩,⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩,⟨33,(8),[1,2,13,14],[190],3⟩,⟨33,(8),[1,2,13,14],[147],98⟩,⟨33,(8),[1,5],[134],97⟩,⟨33,(8),[1,5,13],[135],97⟩,⟨33,(8),[1,13],[151],98⟩,⟨33,(9),[1,2,5,6],[130],98⟩,⟨33,(9),[1,2,5,6,13,14],[131],98⟩,⟨33,(9),[1,2,5,6,13,14],[146,150],159⟩,⟨33,(9),[1,2,13,14],[190],3⟩,⟨33,(9),[1,2,13,14],[147],159⟩,⟨33,(9),[1,5],[134],98⟩,⟨33,(9),[1,5,13],[135],98⟩,⟨33,(9),[1,13],[151],159⟩,⟨33,(10),[1],[134,135],3⟩,⟨33,(10),[1,2],[130,131],3⟩,⟨33,(10),[1,2,5,6,13,14],[146,150],3⟩,⟨33,(10),[1,2,13,14],[147],3⟩,⟨33,(10),[1,2,13,14],[190],29⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1280
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1281
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1282
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1283
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1284
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1285
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1286
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1287
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1288
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1289
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1290
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1291
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1292
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1293
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1294
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1295
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1296
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1297
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1298
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1299
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1300
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1301
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1302
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1303
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1304
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1305
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1306
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1307
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1308
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1309
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1310
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1311
end Section14Records_1_1280_1312

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1280_1312


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1312_1344
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1312_1344
private theorem valid1312 : RecordDataValid section14Catalog 1 (⟨33,(10),[1,13],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1313 : RecordDataValid section14Catalog 1 (⟨33,(11),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1314 : RecordDataValid section14Catalog 1 (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1315 : RecordDataValid section14Catalog 1 (⟨33,(11),[1,2,13,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1316 : RecordDataValid section14Catalog 1 (⟨33,(11),[1,2,13,14],[190],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1317 : RecordDataValid section14Catalog 1 (⟨33,(11),[1,5],[134],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1318 : RecordDataValid section14Catalog 1 (⟨33,(11),[1,5,13],[135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1319 : RecordDataValid section14Catalog 1 (⟨33,(11),[1,13],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1320 : RecordDataValid section14Catalog 1 (⟨33,(12),[1],[151],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1321 : RecordDataValid section14Catalog 1 (⟨33,(12),[1,2],[147],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1322 : RecordDataValid section14Catalog 1 (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1323 : RecordDataValid section14Catalog 1 (⟨33,(12),[1,2,5,6,13,14],[131],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1324 : RecordDataValid section14Catalog 1 (⟨33,(12),[1,2,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1325 : RecordDataValid section14Catalog 1 (⟨33,(12),[1,5],[134],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1326 : RecordDataValid section14Catalog 1 (⟨33,(12),[1,5,13],[135],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1327 : RecordDataValid section14Catalog 1 (⟨33,(13),[1,2,5,6],[130,131],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1328 : RecordDataValid section14Catalog 1 (⟨33,(13),[1,2,5,6,13,14],[146,150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1329 : RecordDataValid section14Catalog 1 (⟨33,(13),[1,2,13,14],[147],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1330 : RecordDataValid section14Catalog 1 (⟨33,(13),[1,2,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1331 : RecordDataValid section14Catalog 1 (⟨33,(13),[1,5],[134,135],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1332 : RecordDataValid section14Catalog 1 (⟨33,(13),[1,13],[151],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1333 : RecordDataValid section14Catalog 1 (⟨33,(14),[1],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1334 : RecordDataValid section14Catalog 1 (⟨33,(14),[1,2,5],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1335 : RecordDataValid section14Catalog 1 (⟨33,(14),[1,2,5,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1336 : RecordDataValid section14Catalog 1 (⟨33,(14),[1,2,13],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1337 : RecordDataValid section14Catalog 1 (⟨33,(14),[1,2,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1338 : RecordDataValid section14Catalog 1 (⟨33,(14),[1,5],[134,135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1339 : RecordDataValid section14Catalog 1 (⟨33,(15),[1],[151],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1340 : RecordDataValid section14Catalog 1 (⟨33,(15),[1,2,5],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1341 : RecordDataValid section14Catalog 1 (⟨33,(15),[1,2,5,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1342 : RecordDataValid section14Catalog 1 (⟨33,(15),[1,2,13,14],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1343 : RecordDataValid section14Catalog 1 (⟨33,(15),[1,2,14],[147],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1312_1344 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1312).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1312).take 32 = [⟨33,(10),[1,13],[151],3⟩,⟨33,(11),[1,2,5,6],[130],3⟩,⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩,⟨33,(11),[1,2,13,14],[147],3⟩,⟨33,(11),[1,2,13,14],[190],234⟩,⟨33,(11),[1,5],[134],3⟩,⟨33,(11),[1,5,13],[135],3⟩,⟨33,(11),[1,13],[151],3⟩,⟨33,(12),[1],[151],99⟩,⟨33,(12),[1,2],[147],99⟩,⟨33,(12),[1,2,5,6],[130,146,150],99⟩,⟨33,(12),[1,2,5,6,13,14],[131],99⟩,⟨33,(12),[1,2,14],[190],3⟩,⟨33,(12),[1,5],[134],99⟩,⟨33,(12),[1,5,13],[135],99⟩,⟨33,(13),[1,2,5,6],[130,131],99⟩,⟨33,(13),[1,2,5,6,13,14],[146,150],99⟩,⟨33,(13),[1,2,13,14],[147],99⟩,⟨33,(13),[1,2,14],[190],3⟩,⟨33,(13),[1,5],[134,135],99⟩,⟨33,(13),[1,13],[151],99⟩,⟨33,(14),[1],[151],3⟩,⟨33,(14),[1,2,5],[130],3⟩,⟨33,(14),[1,2,5,14],[131,146,150],3⟩,⟨33,(14),[1,2,13],[190],99⟩,⟨33,(14),[1,2,14],[147],3⟩,⟨33,(14),[1,5],[134,135],3⟩,⟨33,(15),[1],[151],3⟩,⟨33,(15),[1,2,5],[130],3⟩,⟨33,(15),[1,2,5,14],[131,146,150],3⟩,⟨33,(15),[1,2,13,14],[190],99⟩,⟨33,(15),[1,2,14],[147],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1312
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1313
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1314
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1315
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1316
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1317
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1318
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1319
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1320
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1321
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1322
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1323
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1324
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1325
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1326
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1327
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1328
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1329
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1330
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1331
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1332
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1333
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1334
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1335
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1336
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1337
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1338
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1339
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1340
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1341
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1342
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1343
end Section14Records_1_1312_1344

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1312_1344


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1344_1376
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1344_1376
private theorem valid1344 : RecordDataValid section14Catalog 1 (⟨33,(15),[1,5],[134,135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1345 : RecordDataValid section14Catalog 1 (⟨35,(0),[1],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1346 : RecordDataValid section14Catalog 1 (⟨35,(0),[1,2],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1347 : RecordDataValid section14Catalog 1 (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1348 : RecordDataValid section14Catalog 1 (⟨35,(0),[1,5],[134,135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1349 : RecordDataValid section14Catalog 1 (⟨35,(1),[1],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1350 : RecordDataValid section14Catalog 1 (⟨35,(1),[1,2],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1351 : RecordDataValid section14Catalog 1 (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1352 : RecordDataValid section14Catalog 1 (⟨35,(1),[1,5],[134,135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1353 : RecordDataValid section14Catalog 1 (⟨35,(2),[1],[146],100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨100,[1,5,9],100⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1354 : RecordDataValid section14Catalog 1 (⟨35,(2),[1],[151],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1355 : RecordDataValid section14Catalog 1 (⟨35,(2),[1,2],[147],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1356 : RecordDataValid section14Catalog 1 (⟨35,(2),[1,2],[190],235⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨235,[1,2,3],235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1357 : RecordDataValid section14Catalog 1 (⟨35,(2),[1,2,5,6],[131],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1358 : RecordDataValid section14Catalog 1 (⟨35,(2),[1,2,5,6],[150],139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨139,[1,2,3,5,6,7],139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1359 : RecordDataValid section14Catalog 1 (⟨35,(2),[1,5],[130],100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨100,[1,5,9],100⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1360 : RecordDataValid section14Catalog 1 (⟨35,(2),[1,5],[135],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1361 : RecordDataValid section14Catalog 1 (⟨35,(2),[1,5],[134],139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨139,[1,2,3,5,6,7],139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1362 : RecordDataValid section14Catalog 1 (⟨35,(3),[1],[151],139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨139,[1,2,3,5,6,7],139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1363 : RecordDataValid section14Catalog 1 (⟨35,(3),[1],[147],185⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨185,[1,5,9,10],185⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1364 : RecordDataValid section14Catalog 1 (⟨35,(3),[1,2],[190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1365 : RecordDataValid section14Catalog 1 (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1366 : RecordDataValid section14Catalog 1 (⟨35,(3),[1,2,5,6],[131],121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨121,[1,2,3,5,6,7,9,10,11],121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1367 : RecordDataValid section14Catalog 1 (⟨35,(3),[1,5],[134],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1368 : RecordDataValid section14Catalog 1 (⟨35,(3),[1,5],[135],139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨139,[1,2,3,5,6,7],139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1369 : RecordDataValid section14Catalog 1 (⟨35,(4),[1],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1370 : RecordDataValid section14Catalog 1 (⟨35,(4),[1,2],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1371 : RecordDataValid section14Catalog 1 (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1372 : RecordDataValid section14Catalog 1 (⟨35,(4),[1,5],[134,135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1373 : RecordDataValid section14Catalog 1 (⟨35,(5),[1],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1374 : RecordDataValid section14Catalog 1 (⟨35,(5),[1,2],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1375 : RecordDataValid section14Catalog 1 (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1344_1376 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1344).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1344).take 32 = [⟨33,(15),[1,5],[134,135],3⟩,⟨35,(0),[1],[151],2⟩,⟨35,(0),[1,2],[147,190],2⟩,⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(0),[1,5],[134,135],2⟩,⟨35,(1),[1],[151],2⟩,⟨35,(1),[1,2],[147,190],2⟩,⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(1),[1,5],[134,135],2⟩,⟨35,(2),[1],[146],100⟩,⟨35,(2),[1],[151],101⟩,⟨35,(2),[1,2],[147],101⟩,⟨35,(2),[1,2],[190],235⟩,⟨35,(2),[1,2,5,6],[131],101⟩,⟨35,(2),[1,2,5,6],[150],139⟩,⟨35,(2),[1,5],[130],100⟩,⟨35,(2),[1,5],[135],101⟩,⟨35,(2),[1,5],[134],139⟩,⟨35,(3),[1],[151],139⟩,⟨35,(3),[1],[147],185⟩,⟨35,(3),[1,2],[190],101⟩,⟨35,(3),[1,2,5,6],[130,146,150],101⟩,⟨35,(3),[1,2,5,6],[131],121⟩,⟨35,(3),[1,5],[134],101⟩,⟨35,(3),[1,5],[135],139⟩,⟨35,(4),[1],[151],2⟩,⟨35,(4),[1,2],[147,190],2⟩,⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(4),[1,5],[134,135],2⟩,⟨35,(5),[1],[151],2⟩,⟨35,(5),[1,2],[147,190],2⟩,⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1344
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1345
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1346
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1347
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1348
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1349
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1350
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1351
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1352
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1353
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1354
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1355
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1356
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1357
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1358
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1359
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1360
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1361
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1362
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1363
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1364
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1365
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1366
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1367
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1368
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1369
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1370
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1371
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1372
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1373
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1374
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1375
end Section14Records_1_1344_1376

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1344_1376


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1376_1408
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1376_1408
private theorem valid1376 : RecordDataValid section14Catalog 1 (⟨35,(5),[1,5],[134,135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1377 : RecordDataValid section14Catalog 1 (⟨35,(6),[1],[151],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1378 : RecordDataValid section14Catalog 1 (⟨35,(6),[1],[146],102⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨102,[1,5,9],102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1379 : RecordDataValid section14Catalog 1 (⟨35,(6),[1,2],[147],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1380 : RecordDataValid section14Catalog 1 (⟨35,(6),[1,2],[190],236⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨236,[1,2,3],236⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1381 : RecordDataValid section14Catalog 1 (⟨35,(6),[1,2,5,6],[131],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1382 : RecordDataValid section14Catalog 1 (⟨35,(6),[1,2,5,6],[150],140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨140,[1,2,3,5,6,7],140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1383 : RecordDataValid section14Catalog 1 (⟨35,(6),[1,5],[135],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1384 : RecordDataValid section14Catalog 1 (⟨35,(6),[1,5],[130],102⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨102,[1,5,9],102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1385 : RecordDataValid section14Catalog 1 (⟨35,(6),[1,5],[134],140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨140,[1,2,3,5,6,7],140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1386 : RecordDataValid section14Catalog 1 (⟨35,(7),[1],[151],140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨140,[1,2,3,5,6,7],140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1387 : RecordDataValid section14Catalog 1 (⟨35,(7),[1],[147],186⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨186,[1,5,9,10],186⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1388 : RecordDataValid section14Catalog 1 (⟨35,(7),[1,2],[190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1389 : RecordDataValid section14Catalog 1 (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1390 : RecordDataValid section14Catalog 1 (⟨35,(7),[1,2,5,6],[131],122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨122,[1,2,3,5,6,7,9,10,11],122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1391 : RecordDataValid section14Catalog 1 (⟨35,(7),[1,5],[134],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1392 : RecordDataValid section14Catalog 1 (⟨35,(7),[1,5],[135],140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨140,[1,2,3,5,6,7],140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1393 : RecordDataValid section14Catalog 1 (⟨35,(8),[1],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1394 : RecordDataValid section14Catalog 1 (⟨35,(8),[1,2],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1395 : RecordDataValid section14Catalog 1 (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1396 : RecordDataValid section14Catalog 1 (⟨35,(8),[1,5],[134,135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1397 : RecordDataValid section14Catalog 1 (⟨35,(9),[1],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1398 : RecordDataValid section14Catalog 1 (⟨35,(9),[1,2],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1399 : RecordDataValid section14Catalog 1 (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1400 : RecordDataValid section14Catalog 1 (⟨35,(9),[1,5],[134,135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1401 : RecordDataValid section14Catalog 1 (⟨35,(10),[1],[151],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1402 : RecordDataValid section14Catalog 1 (⟨35,(10),[1],[146],103⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨103,[1,5,9],103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1403 : RecordDataValid section14Catalog 1 (⟨35,(10),[1,2],[147],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1404 : RecordDataValid section14Catalog 1 (⟨35,(10),[1,2],[190],237⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨237,[1,2],237⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1405 : RecordDataValid section14Catalog 1 (⟨35,(10),[1,2,5,6],[131],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1406 : RecordDataValid section14Catalog 1 (⟨35,(10),[1,2,5,6],[150],141⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨141,[1,2,5,6],141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1407 : RecordDataValid section14Catalog 1 (⟨35,(10),[1,5],[135],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1376_1408 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1376).take 32 = [⟨35,(5),[1,5],[134,135],2⟩,⟨35,(6),[1],[151],101⟩,⟨35,(6),[1],[146],102⟩,⟨35,(6),[1,2],[147],101⟩,⟨35,(6),[1,2],[190],236⟩,⟨35,(6),[1,2,5,6],[131],101⟩,⟨35,(6),[1,2,5,6],[150],140⟩,⟨35,(6),[1,5],[135],101⟩,⟨35,(6),[1,5],[130],102⟩,⟨35,(6),[1,5],[134],140⟩,⟨35,(7),[1],[151],140⟩,⟨35,(7),[1],[147],186⟩,⟨35,(7),[1,2],[190],101⟩,⟨35,(7),[1,2,5,6],[130,146,150],101⟩,⟨35,(7),[1,2,5,6],[131],122⟩,⟨35,(7),[1,5],[134],101⟩,⟨35,(7),[1,5],[135],140⟩,⟨35,(8),[1],[151],2⟩,⟨35,(8),[1,2],[147,190],2⟩,⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(8),[1,5],[134,135],2⟩,⟨35,(9),[1],[151],2⟩,⟨35,(9),[1,2],[147,190],2⟩,⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(9),[1,5],[134,135],2⟩,⟨35,(10),[1],[151],101⟩,⟨35,(10),[1],[146],103⟩,⟨35,(10),[1,2],[147],101⟩,⟨35,(10),[1,2],[190],237⟩,⟨35,(10),[1,2,5,6],[131],101⟩,⟨35,(10),[1,2,5,6],[150],141⟩,⟨35,(10),[1,5],[135],101⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1376
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1377
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1378
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1379
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1380
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1381
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1382
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1383
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1384
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1385
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1386
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1387
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1388
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1389
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1390
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1391
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1392
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1393
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1394
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1395
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1396
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1397
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1398
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1399
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1400
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1401
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1402
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1403
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1404
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1405
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1406
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1407
end Section14Records_1_1376_1408

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1376_1408

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1152).take 256, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 1152 1280 1408 (by decide) (by decide) (all_of_interval_split P xs 1152 1216 1280 (by decide) (by decide) (all_of_interval_split P xs 1152 1184 1216 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1152_1184 hnum) (Freiman.workReverse20260919_s0001_records_1184_1216 hnum)) (all_of_interval_split P xs 1216 1248 1280 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1216_1248 hnum) (Freiman.workReverse20260919_s0001_records_1248_1280 hnum))) (all_of_interval_split P xs 1280 1344 1408 (by decide) (by decide) (all_of_interval_split P xs 1280 1312 1344 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1280_1312 hnum) (Freiman.workReverse20260919_s0001_records_1312_1344 hnum)) (all_of_interval_split P xs 1344 1376 1408 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1344_1376 hnum) (Freiman.workReverse20260919_s0001_records_1376_1408 hnum))))

#print axioms solution
