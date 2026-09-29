-- Prove2me | solution 1 for Freiman.section14_s0015_records_1440_1472
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:24:50.576697+00:00
-- url     : https://prove2.me/submissions/754d225f-9ddf-4ba6-bc70-fac9e4ae4101

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
namespace Section14Records_15_1440_1472
private theorem valid1440 : RecordDataValid section14Catalog 15 (⟨441,(10),[3,7,15],[10],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1441 : RecordDataValid section14Catalog 15 (⟨441,(11),[3,7,15],[10],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1442 : RecordDataValid section14Catalog 15 (⟨441,(12),[3,7,15],[10],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1443 : RecordDataValid section14Catalog 15 (⟨441,(13),[3,7,15],[10],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1444 : RecordDataValid section14Catalog 15 (⟨441,(14),[3,7,15],[10],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1445 : RecordDataValid section14Catalog 15 (⟨441,(15),[3,7,15],[10],1140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1140,[3,5,7,8,9,11,12,15],1144⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1446 : RecordDataValid section14Catalog 15 (⟨441,(16),[3,7,15],[10],1141⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1141,[3,5,7,8,9,11,12,15],1145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1447 : RecordDataValid section14Catalog 15 (⟨441,(17),[3,7,15],[10],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1448 : RecordDataValid section14Catalog 15 (⟨441,(18),[3,7,15],[10],1143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1143,[3,5,7,8,9,11,12,15],1147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1449 : RecordDataValid section14Catalog 15 (⟨441,(19),[3,7,15],[10],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1450 : RecordDataValid section14Catalog 15 (⟨441,(20),[3,7,15],[10],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1451 : RecordDataValid section14Catalog 15 (⟨441,(21),[3,7,15],[10],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1452 : RecordDataValid section14Catalog 15 (⟨441,(22),[3,7,15],[10],1144⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1144,[3,5,7,8,9,11,12,15],1148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1453 : RecordDataValid section14Catalog 15 (⟨441,(23),[3,7,15],[10],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1454 : RecordDataValid section14Catalog 15 (⟨441,(24),[3,7,15],[10],1144⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1144,[3,5,7,8,9,11,12,15],1148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1455 : RecordDataValid section14Catalog 15 (⟨443,(0),[3,7,15],[10],1145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1145,[3,7,11,15],1149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1456 : RecordDataValid section14Catalog 15 (⟨443,(1),[3,7,15],[10],1145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1145,[3,7,11,15],1149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1457 : RecordDataValid section14Catalog 15 (⟨443,(2),[3,7,15],[10],1146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1146,[3,7,11,15],1150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1458 : RecordDataValid section14Catalog 15 (⟨443,(3),[3,7,15],[10],1147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1147,[3,7,11,15],1151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1459 : RecordDataValid section14Catalog 15 (⟨443,(4),[3,7,15],[10],1148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1148,[3,7,11,15],1152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1460 : RecordDataValid section14Catalog 15 (⟨443,(5),[3,7,15],[10],1149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1149,[3,7,11,15],1153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1461 : RecordDataValid section14Catalog 15 (⟨443,(6),[3,7,15],[10],1149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1149,[3,7,11,15],1153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1462 : RecordDataValid section14Catalog 15 (⟨443,(7),[3,7,15],[10],1146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1146,[3,7,11,15],1150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1463 : RecordDataValid section14Catalog 15 (⟨443,(8),[3,7,15],[10],1147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1147,[3,7,11,15],1151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1464 : RecordDataValid section14Catalog 15 (⟨443,(9),[3,7,15],[10],1148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1148,[3,7,11,15],1152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1465 : RecordDataValid section14Catalog 15 (⟨443,(10),[3,7,15],[10],1145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1145,[3,7,11,15],1149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1466 : RecordDataValid section14Catalog 15 (⟨443,(11),[3,7,15],[10],1145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1145,[3,7,11,15],1149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1467 : RecordDataValid section14Catalog 15 (⟨443,(12),[3,7,15],[10],1146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1146,[3,7,11,15],1150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1468 : RecordDataValid section14Catalog 15 (⟨443,(13),[3,7,15],[10],1147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1147,[3,7,11,15],1151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1469 : RecordDataValid section14Catalog 15 (⟨443,(14),[3,7,15],[10],1148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1148,[3,7,11,15],1152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1470 : RecordDataValid section14Catalog 15 (⟨443,(15),[3,7,15],[10],1150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1150,[3,7,11,15],1154⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1471 : RecordDataValid section14Catalog 15 (⟨443,(16),[3,7,15],[10],1150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1150,[3,7,11,15],1154⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1440).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1440).take 32 = [⟨441,(10),[3,7,15],[10],1134⟩,⟨441,(11),[3,7,15],[10],1135⟩,⟨441,(12),[3,7,15],[10],1139⟩,⟨441,(13),[3,7,15],[10],1138⟩,⟨441,(14),[3,7,15],[10],1139⟩,⟨441,(15),[3,7,15],[10],1140⟩,⟨441,(16),[3,7,15],[10],1141⟩,⟨441,(17),[3,7,15],[10],1142⟩,⟨441,(18),[3,7,15],[10],1143⟩,⟨441,(19),[3,7,15],[10],1142⟩,⟨441,(20),[3,7,15],[10],1134⟩,⟨441,(21),[3,7,15],[10],1135⟩,⟨441,(22),[3,7,15],[10],1144⟩,⟨441,(23),[3,7,15],[10],1138⟩,⟨441,(24),[3,7,15],[10],1144⟩,⟨443,(0),[3,7,15],[10],1145⟩,⟨443,(1),[3,7,15],[10],1145⟩,⟨443,(2),[3,7,15],[10],1146⟩,⟨443,(3),[3,7,15],[10],1147⟩,⟨443,(4),[3,7,15],[10],1148⟩,⟨443,(5),[3,7,15],[10],1149⟩,⟨443,(6),[3,7,15],[10],1149⟩,⟨443,(7),[3,7,15],[10],1146⟩,⟨443,(8),[3,7,15],[10],1147⟩,⟨443,(9),[3,7,15],[10],1148⟩,⟨443,(10),[3,7,15],[10],1145⟩,⟨443,(11),[3,7,15],[10],1145⟩,⟨443,(12),[3,7,15],[10],1146⟩,⟨443,(13),[3,7,15],[10],1147⟩,⟨443,(14),[3,7,15],[10],1148⟩,⟨443,(15),[3,7,15],[10],1150⟩,⟨443,(16),[3,7,15],[10],1150⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1440
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1441
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1442
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1443
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1444
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1445
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1446
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1447
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1448
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1449
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1450
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1451
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1452
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1453
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1454
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1455
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1456
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1457
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1458
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1459
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1460
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1461
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1462
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1463
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1464
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1465
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1466
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1467
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1468
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1469
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1470
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1471
end Section14Records_15_1440_1472

#print axioms solution
