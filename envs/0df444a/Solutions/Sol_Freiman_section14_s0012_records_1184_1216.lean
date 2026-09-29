-- Prove2me | solution 1 for Freiman.section14_s0012_records_1184_1216
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:49:05.357823+00:00
-- url     : https://prove2.me/submissions/e14956fe-d61d-4426-90af-d0257e4d17c8

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
namespace Section14Records_12_1184_1216
private theorem valid1184 : RecordDataValid section14Catalog 12 (⟨190,(5),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1185 : RecordDataValid section14Catalog 12 (⟨190,(6),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1186 : RecordDataValid section14Catalog 12 (⟨190,(7),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1187 : RecordDataValid section14Catalog 12 (⟨190,(8),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1188 : RecordDataValid section14Catalog 12 (⟨190,(9),[3,4,8,12,15,16],[10],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1189 : RecordDataValid section14Catalog 12 (⟨190,(10),[3,4,8,12,15,16],[10],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1190 : RecordDataValid section14Catalog 12 (⟨190,(11),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1191 : RecordDataValid section14Catalog 12 (⟨190,(12),[3,4,8,12,15,16],[10],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1192 : RecordDataValid section14Catalog 12 (⟨190,(13),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1193 : RecordDataValid section14Catalog 12 (⟨190,(14),[3,4,8,12,15,16],[10],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1194 : RecordDataValid section14Catalog 12 (⟨190,(15),[3,4,8,12,15,16],[10],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1195 : RecordDataValid section14Catalog 12 (⟨190,(16),[3,4,8,12,15,16],[10],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1196 : RecordDataValid section14Catalog 12 (⟨190,(17),[3,4,8,12,15,16],[10],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1197 : RecordDataValid section14Catalog 12 (⟨190,(18),[3,4,8,12,15,16],[10],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1198 : RecordDataValid section14Catalog 12 (⟨190,(19),[3,4,8,12,15,16],[10],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1199 : RecordDataValid section14Catalog 12 (⟨190,(20),[3,4,8,12,15,16],[10],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1200 : RecordDataValid section14Catalog 12 (⟨190,(21),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1201 : RecordDataValid section14Catalog 12 (⟨190,(22),[3,4,8,12,15,16],[10],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1202 : RecordDataValid section14Catalog 12 (⟨190,(23),[3,4,8,12,15,16],[10],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1203 : RecordDataValid section14Catalog 12 (⟨190,(24),[3,4,8,12,15,16],[10],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1204 : RecordDataValid section14Catalog 12 (⟨192,(0),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1205 : RecordDataValid section14Catalog 12 (⟨192,(1),[4,8,12,16],[10],1316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1316,[4,8,9,12,16],1320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1206 : RecordDataValid section14Catalog 12 (⟨192,(2),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1207 : RecordDataValid section14Catalog 12 (⟨192,(3),[4,8,12,16],[10],1317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1317,[4,8,9,12,16],1321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1208 : RecordDataValid section14Catalog 12 (⟨192,(4),[4,8,12,16],[10],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1209 : RecordDataValid section14Catalog 12 (⟨192,(5),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1210 : RecordDataValid section14Catalog 12 (⟨192,(6),[4,8,12,16],[10],1316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1316,[4,8,9,12,16],1320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1211 : RecordDataValid section14Catalog 12 (⟨192,(7),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1212 : RecordDataValid section14Catalog 12 (⟨192,(8),[4,8,12,16],[10],1317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1317,[4,8,9,12,16],1321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1213 : RecordDataValid section14Catalog 12 (⟨192,(9),[4,8,12,16],[10],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1214 : RecordDataValid section14Catalog 12 (⟨192,(10),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1215 : RecordDataValid section14Catalog 12 (⟨192,(11),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1184).take 32 = [⟨190,(5),[3,4,8,12,15,16],[10],691⟩,⟨190,(6),[3,4,8,12,15,16],[10],691⟩,⟨190,(7),[3,4,8,12,15,16],[10],691⟩,⟨190,(8),[3,4,8,12,15,16],[10],691⟩,⟨190,(9),[3,4,8,12,15,16],[10],691⟩,⟨190,(10),[3,4,8,12,15,16],[10],692⟩,⟨190,(11),[3,4,8,12,15,16],[10],693⟩,⟨190,(12),[3,4,8,12,15,16],[10],694⟩,⟨190,(13),[3,4,8,12,15,16],[10],693⟩,⟨190,(14),[3,4,8,12,15,16],[10],695⟩,⟨190,(15),[3,4,8,12,15,16],[10],692⟩,⟨190,(16),[3,4,8,12,15,16],[10],696⟩,⟨190,(17),[3,4,8,12,15,16],[10],696⟩,⟨190,(18),[3,4,8,12,15,16],[10],696⟩,⟨190,(19),[3,4,8,12,15,16],[10],696⟩,⟨190,(20),[3,4,8,12,15,16],[10],692⟩,⟨190,(21),[3,4,8,12,15,16],[10],693⟩,⟨190,(22),[3,4,8,12,15,16],[10],694⟩,⟨190,(23),[3,4,8,12,15,16],[10],693⟩,⟨190,(24),[3,4,8,12,15,16],[10],695⟩,⟨192,(0),[4,8,12,16],[10],1315⟩,⟨192,(1),[4,8,12,16],[10],1316⟩,⟨192,(2),[4,8,12,16],[10],1315⟩,⟨192,(3),[4,8,12,16],[10],1317⟩,⟨192,(4),[4,8,12,16],[10],1318⟩,⟨192,(5),[4,8,12,16],[10],1315⟩,⟨192,(6),[4,8,12,16],[10],1316⟩,⟨192,(7),[4,8,12,16],[10],1315⟩,⟨192,(8),[4,8,12,16],[10],1317⟩,⟨192,(9),[4,8,12,16],[10],1318⟩,⟨192,(10),[4,8,12,16],[10],1319⟩,⟨192,(11),[4,8,12,16],[10],1319⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1184
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1185
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1186
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1187
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1188
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1189
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1190
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1191
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1192
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1193
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1194
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1195
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1196
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1197
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1198
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1199
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1200
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1201
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1202
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1203
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1204
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1205
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1206
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1207
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1208
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1209
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1210
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1211
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1212
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1213
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1214
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1215
end Section14Records_12_1184_1216

#print axioms solution
