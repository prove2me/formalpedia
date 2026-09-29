-- Prove2me | solution 1 for Freiman.section14_s0015_records_1376_1408
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:23:23.4684+00:00
-- url     : https://prove2.me/submissions/81596e7a-cc8e-4aaf-9686-714f9cd2e54e

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
namespace Section14Records_15_1376_1408
private theorem valid1376 : RecordDataValid section14Catalog 15 (⟨431,(16),[3,7,15],[10],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1377 : RecordDataValid section14Catalog 15 (⟨431,(17),[3,7,15],[10],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1378 : RecordDataValid section14Catalog 15 (⟨431,(18),[3,7,15],[10],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1379 : RecordDataValid section14Catalog 15 (⟨431,(19),[3,7,15],[10],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1380 : RecordDataValid section14Catalog 15 (⟨431,(20),[3,7,15],[10],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1381 : RecordDataValid section14Catalog 15 (⟨431,(21),[3,7,15],[10],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1382 : RecordDataValid section14Catalog 15 (⟨431,(22),[3,7,15],[10],1114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1114,[3,5,7,8,9,11,12,15],1118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1383 : RecordDataValid section14Catalog 15 (⟨431,(23),[3,7,15],[10],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1384 : RecordDataValid section14Catalog 15 (⟨431,(24),[3,7,15],[10],1114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1114,[3,5,7,8,9,11,12,15],1118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1385 : RecordDataValid section14Catalog 15 (⟨433,(0),[3,7,15],[10],1115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1115,[3,7,11,15],1119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1386 : RecordDataValid section14Catalog 15 (⟨433,(1),[3,7,15],[10],1115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1115,[3,7,11,15],1119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1387 : RecordDataValid section14Catalog 15 (⟨433,(2),[3,7,15],[10],1116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1116,[3,7,11,15],1120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1388 : RecordDataValid section14Catalog 15 (⟨433,(3),[3,7,15],[10],1117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1117,[3,7,11,15],1121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1389 : RecordDataValid section14Catalog 15 (⟨433,(4),[3,7,15],[10],1118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1118,[3,7,11,15],1122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1390 : RecordDataValid section14Catalog 15 (⟨433,(5),[3,7,15],[10],1119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1119,[3,7,11,15],1123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1391 : RecordDataValid section14Catalog 15 (⟨433,(6),[3,7,15],[10],1119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1119,[3,7,11,15],1123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1392 : RecordDataValid section14Catalog 15 (⟨433,(7),[3,7,15],[10],1119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1119,[3,7,11,15],1123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1393 : RecordDataValid section14Catalog 15 (⟨433,(8),[3,7,15],[10],1117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1117,[3,7,11,15],1121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1394 : RecordDataValid section14Catalog 15 (⟨433,(9),[3,7,15],[10],1118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1118,[3,7,11,15],1122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1395 : RecordDataValid section14Catalog 15 (⟨436,(0),[3,7,15],[10],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1396 : RecordDataValid section14Catalog 15 (⟨436,(1),[3,7,15],[10],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1397 : RecordDataValid section14Catalog 15 (⟨436,(2),[3,7,15],[10],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1398 : RecordDataValid section14Catalog 15 (⟨436,(3),[3,7,15],[10],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1399 : RecordDataValid section14Catalog 15 (⟨436,(4),[3,7,15],[10],1123⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1123,[3,5,7,8,9,11,12,15],1127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1400 : RecordDataValid section14Catalog 15 (⟨436,(5),[3,7,15],[10],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1401 : RecordDataValid section14Catalog 15 (⟨436,(6),[3,7,15],[10],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1402 : RecordDataValid section14Catalog 15 (⟨436,(7),[3,7,15],[10],1124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1124,[3,5,7,8,9,11,12,15],1128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1403 : RecordDataValid section14Catalog 15 (⟨436,(8),[3,7,15],[10],1125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1125,[3,5,7,8,9,11,12,15],1129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1404 : RecordDataValid section14Catalog 15 (⟨436,(9),[3,7,15],[10],1126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1126,[3,5,7,8,9,11,12,15],1130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1405 : RecordDataValid section14Catalog 15 (⟨438,(0),[3,7,15],[10],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1406 : RecordDataValid section14Catalog 15 (⟨438,(1),[3,7,15],[10],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1407 : RecordDataValid section14Catalog 15 (⟨438,(2),[3,7,15],[10],1128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1128,[3,7,11,15],1132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1376).take 32 = [⟨431,(16),[3,7,15],[10],1109⟩,⟨431,(17),[3,7,15],[10],1111⟩,⟨431,(18),[3,7,15],[10],1112⟩,⟨431,(19),[3,7,15],[10],1111⟩,⟨431,(20),[3,7,15],[10],1108⟩,⟨431,(21),[3,7,15],[10],1109⟩,⟨431,(22),[3,7,15],[10],1114⟩,⟨431,(23),[3,7,15],[10],1112⟩,⟨431,(24),[3,7,15],[10],1114⟩,⟨433,(0),[3,7,15],[10],1115⟩,⟨433,(1),[3,7,15],[10],1115⟩,⟨433,(2),[3,7,15],[10],1116⟩,⟨433,(3),[3,7,15],[10],1117⟩,⟨433,(4),[3,7,15],[10],1118⟩,⟨433,(5),[3,7,15],[10],1119⟩,⟨433,(6),[3,7,15],[10],1119⟩,⟨433,(7),[3,7,15],[10],1119⟩,⟨433,(8),[3,7,15],[10],1117⟩,⟨433,(9),[3,7,15],[10],1118⟩,⟨436,(0),[3,7,15],[10],1120⟩,⟨436,(1),[3,7,15],[10],1121⟩,⟨436,(2),[3,7,15],[10],1122⟩,⟨436,(3),[3,7,15],[10],1122⟩,⟨436,(4),[3,7,15],[10],1123⟩,⟨436,(5),[3,7,15],[10],1120⟩,⟨436,(6),[3,7,15],[10],1121⟩,⟨436,(7),[3,7,15],[10],1124⟩,⟨436,(8),[3,7,15],[10],1125⟩,⟨436,(9),[3,7,15],[10],1126⟩,⟨438,(0),[3,7,15],[10],1127⟩,⟨438,(1),[3,7,15],[10],1127⟩,⟨438,(2),[3,7,15],[10],1128⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1376
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1377
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1378
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1379
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1380
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1381
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1382
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1383
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1384
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1385
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1386
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1387
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1388
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1389
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1390
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1391
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1392
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1393
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1394
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1395
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1396
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1397
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1398
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1399
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1400
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1401
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1402
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1403
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1404
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1405
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1406
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1407
end Section14Records_15_1376_1408

#print axioms solution
