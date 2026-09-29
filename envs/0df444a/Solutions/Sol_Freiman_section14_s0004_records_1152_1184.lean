-- Prove2me | solution 1 for Freiman.section14_s0004_records_1152_1184
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:32:39.854416+00:00
-- url     : https://prove2.me/submissions/e56aebf9-2339-4dc9-bfa5-5b01f71905f4

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
namespace Section14Records_4_1152_1184
private theorem valid1152 : RecordDataValid section14Catalog 4 (⟨153,(-1),[4,8,10,12,16],[8,12],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1153 : RecordDataValid section14Catalog 4 (⟨153,(-1),[4,8,11,12,16],[1],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1154 : RecordDataValid section14Catalog 4 (⟨153,(-1),[4,8,12,16],[9,13],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1155 : RecordDataValid section14Catalog 4 (⟨153,(-1),[4,8,12,16],[2],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1156 : RecordDataValid section14Catalog 4 (⟨153,(-1),[4,8,12,16],[7,11,15],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1157 : RecordDataValid section14Catalog 4 (⟨153,(-1),[4,8,12,16],[6],637⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨637,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],638⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1158 : RecordDataValid section14Catalog 4 (⟨153,(-1),[4,8,12,16],[14],879⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨879,[1,2,4,5,6,8,9,10,12,13,14,16],881⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1159 : RecordDataValid section14Catalog 4 (⟨153,(-1),[4,16],[3],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1160 : RecordDataValid section14Catalog 4 (⟨157,(0),[3,4,7,8,15,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1161 : RecordDataValid section14Catalog 4 (⟨157,(1),[4,8,16],[10],1272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1272,[4,8,16],1276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1162 : RecordDataValid section14Catalog 4 (⟨157,(2),[4,8,16],[10],1273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1273,[4,8,16],1277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1163 : RecordDataValid section14Catalog 4 (⟨157,(3),[4,8,16],[10],1274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1274,[4,8,16],1278⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1164 : RecordDataValid section14Catalog 4 (⟨157,(4),[4,8,16],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1165 : RecordDataValid section14Catalog 4 (⟨157,(5),[3,4,7,8,15,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1166 : RecordDataValid section14Catalog 4 (⟨157,(6),[4,8,16],[10],1272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1272,[4,8,16],1276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1167 : RecordDataValid section14Catalog 4 (⟨157,(7),[4,8,16],[10],1273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1273,[4,8,16],1277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1168 : RecordDataValid section14Catalog 4 (⟨157,(8),[4,8,16],[10],1274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1274,[4,8,16],1278⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1169 : RecordDataValid section14Catalog 4 (⟨157,(9),[4,8,16],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1170 : RecordDataValid section14Catalog 4 (⟨157,(10),[3,4,7,8,15,16],[10],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1171 : RecordDataValid section14Catalog 4 (⟨157,(11),[4,8,16],[10],1276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1276,[4,8,16],1280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1172 : RecordDataValid section14Catalog 4 (⟨157,(12),[4,8,16],[10],1276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1276,[4,8,16],1280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1173 : RecordDataValid section14Catalog 4 (⟨157,(13),[4,8,16],[10],1276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1276,[4,8,16],1280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1174 : RecordDataValid section14Catalog 4 (⟨157,(14),[4,8,16],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1175 : RecordDataValid section14Catalog 4 (⟨157,(15),[3,4,7,8,15,16],[10],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1176 : RecordDataValid section14Catalog 4 (⟨157,(16),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1177 : RecordDataValid section14Catalog 4 (⟨157,(17),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1178 : RecordDataValid section14Catalog 4 (⟨157,(18),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1179 : RecordDataValid section14Catalog 4 (⟨157,(19),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1180 : RecordDataValid section14Catalog 4 (⟨157,(20),[3,4,7,8,15,16],[10],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1181 : RecordDataValid section14Catalog 4 (⟨157,(21),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1182 : RecordDataValid section14Catalog 4 (⟨157,(22),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1183 : RecordDataValid section14Catalog 4 (⟨157,(23),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1152).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1152).take 32 = [⟨153,(-1),[4,8,10,12,16],[8,12],632⟩,⟨153,(-1),[4,8,11,12,16],[1],633⟩,⟨153,(-1),[4,8,12,16],[9,13],633⟩,⟨153,(-1),[4,8,12,16],[2],634⟩,⟨153,(-1),[4,8,12,16],[7,11,15],636⟩,⟨153,(-1),[4,8,12,16],[6],637⟩,⟨153,(-1),[4,8,12,16],[14],879⟩,⟨153,(-1),[4,16],[3],634⟩,⟨157,(0),[3,4,7,8,15,16],[10],10⟩,⟨157,(1),[4,8,16],[10],1272⟩,⟨157,(2),[4,8,16],[10],1273⟩,⟨157,(3),[4,8,16],[10],1274⟩,⟨157,(4),[4,8,16],[10],1275⟩,⟨157,(5),[3,4,7,8,15,16],[10],10⟩,⟨157,(6),[4,8,16],[10],1272⟩,⟨157,(7),[4,8,16],[10],1273⟩,⟨157,(8),[4,8,16],[10],1274⟩,⟨157,(9),[4,8,16],[10],1275⟩,⟨157,(10),[3,4,7,8,15,16],[10],18⟩,⟨157,(11),[4,8,16],[10],1276⟩,⟨157,(12),[4,8,16],[10],1276⟩,⟨157,(13),[4,8,16],[10],1276⟩,⟨157,(14),[4,8,16],[10],1275⟩,⟨157,(15),[3,4,7,8,15,16],[10],21⟩,⟨157,(16),[4,8,16],[10],1277⟩,⟨157,(17),[4,8,16],[10],1277⟩,⟨157,(18),[4,8,16],[10],1277⟩,⟨157,(19),[4,8,16],[10],1277⟩,⟨157,(20),[3,4,7,8,15,16],[10],24⟩,⟨157,(21),[4,8,16],[10],1278⟩,⟨157,(22),[4,8,16],[10],1278⟩,⟨157,(23),[4,8,16],[10],1278⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1152
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1153
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1154
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1155
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1156
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1157
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1158
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1159
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1160
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1161
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1162
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1163
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1164
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1165
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1166
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1167
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1168
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1169
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1170
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1171
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1172
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1173
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1174
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1175
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1176
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1177
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1178
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1179
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1180
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1181
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1182
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1183
end Section14Records_4_1152_1184

#print axioms solution
