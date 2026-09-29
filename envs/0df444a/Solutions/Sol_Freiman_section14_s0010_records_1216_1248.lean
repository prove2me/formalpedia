-- Prove2me | solution 1 for Freiman.section14_s0010_records_1216_1248
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T17:01:10.760231+00:00
-- url     : https://prove2.me/submissions/250d4f36-c124-4736-989d-ec6ed5a131d4

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
namespace Section14Records_10_1216_1248
private theorem valid1216 : RecordDataValid section14Catalog 10 (⟨119,(11),[9,10],[42],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1217 : RecordDataValid section14Catalog 10 (⟨119,(12),[9,10],[42],478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨478,[1,4,5,6,8,9,10,12,13,16],479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1218 : RecordDataValid section14Catalog 10 (⟨119,(13),[10],[42],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1219 : RecordDataValid section14Catalog 10 (⟨119,(14),[9,10],[42],479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨479,[1,4,5,6,8,9,10,12,13,16],480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1220 : RecordDataValid section14Catalog 10 (⟨119,(15),[9,10],[42],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1221 : RecordDataValid section14Catalog 10 (⟨119,(16),[9,10],[42],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1222 : RecordDataValid section14Catalog 10 (⟨119,(17),[9,10],[42],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1223 : RecordDataValid section14Catalog 10 (⟨119,(18),[10],[42],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1224 : RecordDataValid section14Catalog 10 (⟨119,(19),[9,10],[42],480⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1225 : RecordDataValid section14Catalog 10 (⟨119,(20),[9,10],[42],476⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1226 : RecordDataValid section14Catalog 10 (⟨119,(21),[9,10],[42],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1227 : RecordDataValid section14Catalog 10 (⟨119,(22),[9,10],[42],478⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨478,[1,4,5,6,8,9,10,12,13,16],479⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1228 : RecordDataValid section14Catalog 10 (⟨119,(23),[10],[42],477⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1229 : RecordDataValid section14Catalog 10 (⟨119,(24),[9,10],[42],479⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨479,[1,4,5,6,8,9,10,12,13,16],480⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1230 : RecordDataValid section14Catalog 10 (⟨121,(0),[9,10],[42],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1231 : RecordDataValid section14Catalog 10 (⟨121,(1),[9,10],[42],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1232 : RecordDataValid section14Catalog 10 (⟨121,(2),[9,10],[42],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1233 : RecordDataValid section14Catalog 10 (⟨121,(3),[9,10],[42],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1234 : RecordDataValid section14Catalog 10 (⟨121,(4),[9,10],[42],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1235 : RecordDataValid section14Catalog 10 (⟨121,(5),[9,10],[42],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1236 : RecordDataValid section14Catalog 10 (⟨121,(6),[9,10],[42],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1237 : RecordDataValid section14Catalog 10 (⟨121,(7),[9,10],[42],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1238 : RecordDataValid section14Catalog 10 (⟨121,(8),[9,10],[42],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1239 : RecordDataValid section14Catalog 10 (⟨121,(9),[9,10],[42],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1240 : RecordDataValid section14Catalog 10 (⟨121,(10),[9,10],[42],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1241 : RecordDataValid section14Catalog 10 (⟨121,(11),[9,10],[42],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1242 : RecordDataValid section14Catalog 10 (⟨121,(12),[9,10],[42],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1243 : RecordDataValid section14Catalog 10 (⟨121,(13),[9,10],[42],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1244 : RecordDataValid section14Catalog 10 (⟨121,(14),[9,10],[42],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1245 : RecordDataValid section14Catalog 10 (⟨121,(15),[9,10],[42],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1246 : RecordDataValid section14Catalog 10 (⟨121,(16),[9,10],[42],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1247 : RecordDataValid section14Catalog 10 (⟨121,(17),[9,10],[42],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1216).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1216).take 32 = [⟨119,(11),[9,10],[42],477⟩,⟨119,(12),[9,10],[42],478⟩,⟨119,(13),[10],[42],477⟩,⟨119,(14),[9,10],[42],479⟩,⟨119,(15),[9,10],[42],476⟩,⟨119,(16),[9,10],[42],480⟩,⟨119,(17),[9,10],[42],480⟩,⟨119,(18),[10],[42],480⟩,⟨119,(19),[9,10],[42],480⟩,⟨119,(20),[9,10],[42],476⟩,⟨119,(21),[9,10],[42],477⟩,⟨119,(22),[9,10],[42],478⟩,⟨119,(23),[10],[42],477⟩,⟨119,(24),[9,10],[42],479⟩,⟨121,(0),[9,10],[42],481⟩,⟨121,(1),[9,10],[42],482⟩,⟨121,(2),[9,10],[42],481⟩,⟨121,(3),[9,10],[42],483⟩,⟨121,(4),[9,10],[42],484⟩,⟨121,(5),[9,10],[42],481⟩,⟨121,(6),[9,10],[42],482⟩,⟨121,(7),[9,10],[42],481⟩,⟨121,(8),[9,10],[42],483⟩,⟨121,(9),[9,10],[42],484⟩,⟨121,(10),[9,10],[42],485⟩,⟨121,(11),[9,10],[42],485⟩,⟨121,(12),[9,10],[42],485⟩,⟨121,(13),[9,10],[42],485⟩,⟨121,(14),[9,10],[42],484⟩,⟨121,(15),[9,10],[42],486⟩,⟨121,(16),[9,10],[42],486⟩,⟨121,(17),[9,10],[42],486⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1216
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1217
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1218
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1219
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1220
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1221
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1222
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1223
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1224
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1225
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1226
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1227
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1228
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1229
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1230
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1231
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1232
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1233
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1234
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1235
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1236
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1237
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1238
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1239
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1240
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1241
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1242
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1243
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1244
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1245
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1246
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1247
end Section14Records_10_1216_1248

#print axioms solution
