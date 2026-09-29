-- Prove2me | solution 1 for Freiman.section14_s0016_records_1152_1184
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:21:46.763353+00:00
-- url     : https://prove2.me/submissions/0cfab1dc-5586-4ec5-8b40-93369a6179ea

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
namespace Section14Records_16_1152_1184
private theorem valid1152 : RecordDataValid section14Catalog 16 (⟨197,(0),[4,8,12,16],[10],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1153 : RecordDataValid section14Catalog 16 (⟨197,(1),[4,8,12,16],[10],1323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1323,[4,8,9,12,16],1327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1154 : RecordDataValid section14Catalog 16 (⟨197,(2),[4,8,12,16],[10],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1155 : RecordDataValid section14Catalog 16 (⟨197,(3),[4,8,12,16],[10],1324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1324,[4,8,9,12,16],1328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1156 : RecordDataValid section14Catalog 16 (⟨197,(4),[4,8,12,16],[10],1325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1325,[4,8,9,12,16],1329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1157 : RecordDataValid section14Catalog 16 (⟨197,(5),[4,8,12,16],[10],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1158 : RecordDataValid section14Catalog 16 (⟨197,(6),[4,8,12,16],[10],1323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1323,[4,8,9,12,16],1327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1159 : RecordDataValid section14Catalog 16 (⟨197,(7),[4,8,12,16],[10],1322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1322,[4,8,9,12,16],1326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1160 : RecordDataValid section14Catalog 16 (⟨197,(8),[4,8,12,16],[10],1324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1324,[4,8,9,12,16],1328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1161 : RecordDataValid section14Catalog 16 (⟨197,(9),[4,8,12,16],[10],1325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1325,[4,8,9,12,16],1329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1162 : RecordDataValid section14Catalog 16 (⟨197,(10),[4,8,12,16],[10],1326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1326,[4,8,9,12,16],1330⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1163 : RecordDataValid section14Catalog 16 (⟨197,(11),[4,8,12,16],[10],1326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1326,[4,8,9,12,16],1330⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1164 : RecordDataValid section14Catalog 16 (⟨197,(12),[4,8,12,16],[10],1326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1326,[4,8,9,12,16],1330⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1165 : RecordDataValid section14Catalog 16 (⟨197,(13),[4,8,12,16],[10],1326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1326,[4,8,9,12,16],1330⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1166 : RecordDataValid section14Catalog 16 (⟨197,(14),[4,8,12,16],[10],1325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1325,[4,8,9,12,16],1329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1167 : RecordDataValid section14Catalog 16 (⟨197,(15),[4,8,12,16],[10],1327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1327,[4,8,9,12,16],1331⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1168 : RecordDataValid section14Catalog 16 (⟨197,(16),[4,8,12,16],[10],1327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1327,[4,8,9,12,16],1331⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1169 : RecordDataValid section14Catalog 16 (⟨197,(17),[4,8,12,16],[10],1327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1327,[4,8,9,12,16],1331⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1170 : RecordDataValid section14Catalog 16 (⟨197,(18),[4,8,12,16],[10],1327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1327,[4,8,9,12,16],1331⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1171 : RecordDataValid section14Catalog 16 (⟨197,(19),[4,8,12,16],[10],1327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1327,[4,8,9,12,16],1331⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1172 : RecordDataValid section14Catalog 16 (⟨197,(20),[4,8,12,16],[10],1328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1328,[4,8,9,12,16],1332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1173 : RecordDataValid section14Catalog 16 (⟨197,(21),[4,8,12,16],[10],1328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1328,[4,8,9,12,16],1332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1174 : RecordDataValid section14Catalog 16 (⟨197,(22),[4,8,12,16],[10],1328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1328,[4,8,9,12,16],1332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1175 : RecordDataValid section14Catalog 16 (⟨197,(23),[4,8,12,16],[10],1328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1328,[4,8,9,12,16],1332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1176 : RecordDataValid section14Catalog 16 (⟨197,(24),[4,8,12,16],[10],1328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1328,[4,8,9,12,16],1332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1177 : RecordDataValid section14Catalog 16 (⟨200,(0),[3,4,8,12,15,16],[10],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1178 : RecordDataValid section14Catalog 16 (⟨200,(1),[3,4,8,12,15,16],[10],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1179 : RecordDataValid section14Catalog 16 (⟨200,(2),[3,4,8,12,15,16],[10],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1180 : RecordDataValid section14Catalog 16 (⟨200,(3),[3,4,8,12,15,16],[10],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1181 : RecordDataValid section14Catalog 16 (⟨200,(4),[3,4,8,12,15,16],[10],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1182 : RecordDataValid section14Catalog 16 (⟨200,(5),[3,4,8,12,15,16],[10],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1183 : RecordDataValid section14Catalog 16 (⟨200,(6),[3,4,8,12,15,16],[10],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1152).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1152).take 32 = [⟨197,(0),[4,8,12,16],[10],1322⟩,⟨197,(1),[4,8,12,16],[10],1323⟩,⟨197,(2),[4,8,12,16],[10],1322⟩,⟨197,(3),[4,8,12,16],[10],1324⟩,⟨197,(4),[4,8,12,16],[10],1325⟩,⟨197,(5),[4,8,12,16],[10],1322⟩,⟨197,(6),[4,8,12,16],[10],1323⟩,⟨197,(7),[4,8,12,16],[10],1322⟩,⟨197,(8),[4,8,12,16],[10],1324⟩,⟨197,(9),[4,8,12,16],[10],1325⟩,⟨197,(10),[4,8,12,16],[10],1326⟩,⟨197,(11),[4,8,12,16],[10],1326⟩,⟨197,(12),[4,8,12,16],[10],1326⟩,⟨197,(13),[4,8,12,16],[10],1326⟩,⟨197,(14),[4,8,12,16],[10],1325⟩,⟨197,(15),[4,8,12,16],[10],1327⟩,⟨197,(16),[4,8,12,16],[10],1327⟩,⟨197,(17),[4,8,12,16],[10],1327⟩,⟨197,(18),[4,8,12,16],[10],1327⟩,⟨197,(19),[4,8,12,16],[10],1327⟩,⟨197,(20),[4,8,12,16],[10],1328⟩,⟨197,(21),[4,8,12,16],[10],1328⟩,⟨197,(22),[4,8,12,16],[10],1328⟩,⟨197,(23),[4,8,12,16],[10],1328⟩,⟨197,(24),[4,8,12,16],[10],1328⟩,⟨200,(0),[3,4,8,12,15,16],[10],704⟩,⟨200,(1),[3,4,8,12,15,16],[10],704⟩,⟨200,(2),[3,4,8,12,15,16],[10],704⟩,⟨200,(3),[3,4,8,12,15,16],[10],704⟩,⟨200,(4),[3,4,8,12,15,16],[10],704⟩,⟨200,(5),[3,4,8,12,15,16],[10],705⟩,⟨200,(6),[3,4,8,12,15,16],[10],705⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1152
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1153
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1154
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1155
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1156
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1157
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1158
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1159
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1160
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1161
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1162
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1163
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1164
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1165
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1166
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1167
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1168
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1169
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1170
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1171
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1172
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1173
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1174
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1175
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1176
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1177
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1178
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1179
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1180
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1181
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1182
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1183
end Section14Records_16_1152_1184

#print axioms solution
