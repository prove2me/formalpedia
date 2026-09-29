-- Prove2me | solution 1 for Freiman.section14_s0016_records_1440_1472
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:34:01.070096+00:00
-- url     : https://prove2.me/submissions/95916ffd-6301-4dff-b96a-a302574a81f6

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
namespace Section14Records_16_1440_1472
private theorem valid1440 : RecordDataValid section14Catalog 16 (⟨227,(1),[3,4,7,8,12,15,16],[10],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1441 : RecordDataValid section14Catalog 16 (⟨227,(2),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1442 : RecordDataValid section14Catalog 16 (⟨227,(3),[3,4,7,8,12,15,16],[10],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1443 : RecordDataValid section14Catalog 16 (⟨227,(4),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1444 : RecordDataValid section14Catalog 16 (⟨227,(5),[3,4,7,8,12,15,16],[10],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1445 : RecordDataValid section14Catalog 16 (⟨227,(6),[3,4,7,8,12,15,16],[10],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1446 : RecordDataValid section14Catalog 16 (⟨227,(7),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1447 : RecordDataValid section14Catalog 16 (⟨227,(8),[3,4,7,8,12,15,16],[10],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1448 : RecordDataValid section14Catalog 16 (⟨227,(9),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1449 : RecordDataValid section14Catalog 16 (⟨227,(10),[3,4,7,8,12,15,16],[10],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1450 : RecordDataValid section14Catalog 16 (⟨227,(11),[3,4,7,8,12,15,16],[10],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1451 : RecordDataValid section14Catalog 16 (⟨227,(12),[4,8,12,16],[10],1372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1372,[4,8,9,12,16],1376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1452 : RecordDataValid section14Catalog 16 (⟨227,(13),[3,4,7,8,12,15,16],[10],780⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1453 : RecordDataValid section14Catalog 16 (⟨227,(14),[4,8,12,16],[10],1372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1372,[4,8,9,12,16],1376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1454 : RecordDataValid section14Catalog 16 (⟨227,(15),[3,4,7,8,12,15,16],[10],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1455 : RecordDataValid section14Catalog 16 (⟨227,(16),[3,4,7,8,12,15,16],[10],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1456 : RecordDataValid section14Catalog 16 (⟨227,(17),[4,8,12,16],[10],1373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1373,[4,8,9,12,16],1377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1457 : RecordDataValid section14Catalog 16 (⟨227,(18),[3,4,7,8,12,15,16],[10],784⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1458 : RecordDataValid section14Catalog 16 (⟨227,(19),[4,8,12,16],[10],1373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1373,[4,8,9,12,16],1377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1459 : RecordDataValid section14Catalog 16 (⟨227,(20),[3,4,7,8,12,15,16],[10],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1460 : RecordDataValid section14Catalog 16 (⟨227,(21),[3,4,7,8,12,15,16],[10],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1461 : RecordDataValid section14Catalog 16 (⟨227,(22),[4,8,12,16],[10],1374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1374,[4,8,9,12,16],1378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1462 : RecordDataValid section14Catalog 16 (⟨227,(23),[3,4,7,8,12,15,16],[10],788⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1463 : RecordDataValid section14Catalog 16 (⟨227,(24),[4,8,12,16],[10],1374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1374,[4,8,9,12,16],1378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1464 : RecordDataValid section14Catalog 16 (⟨228,(0),[3,4,8,12,15,16],[10],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1465 : RecordDataValid section14Catalog 16 (⟨228,(1),[3,4,8,12,15,16],[10],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1466 : RecordDataValid section14Catalog 16 (⟨228,(2),[4,8,12,16],[10],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1467 : RecordDataValid section14Catalog 16 (⟨228,(3),[3,4,8,12,15,16],[10],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1468 : RecordDataValid section14Catalog 16 (⟨228,(4),[3,4,7,8,12,15,16],[10],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1469 : RecordDataValid section14Catalog 16 (⟨228,(5),[3,4,7,8,12,15,16],[10],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1470 : RecordDataValid section14Catalog 16 (⟨228,(6),[3,4,7,8,12,15,16],[10],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1471 : RecordDataValid section14Catalog 16 (⟨228,(7),[3,4,7,8,12,15,16],[10],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1440).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1440).take 32 = [⟨227,(1),[3,4,7,8,12,15,16],[10],774⟩,⟨227,(2),[4,8,12,16],[10],1371⟩,⟨227,(3),[3,4,7,8,12,15,16],[10],776⟩,⟨227,(4),[4,8,12,16],[10],1371⟩,⟨227,(5),[3,4,7,8,12,15,16],[10],773⟩,⟨227,(6),[3,4,7,8,12,15,16],[10],774⟩,⟨227,(7),[4,8,12,16],[10],1371⟩,⟨227,(8),[3,4,7,8,12,15,16],[10],776⟩,⟨227,(9),[4,8,12,16],[10],1371⟩,⟨227,(10),[3,4,7,8,12,15,16],[10],777⟩,⟨227,(11),[3,4,7,8,12,15,16],[10],778⟩,⟨227,(12),[4,8,12,16],[10],1372⟩,⟨227,(13),[3,4,7,8,12,15,16],[10],780⟩,⟨227,(14),[4,8,12,16],[10],1372⟩,⟨227,(15),[3,4,7,8,12,15,16],[10],781⟩,⟨227,(16),[3,4,7,8,12,15,16],[10],782⟩,⟨227,(17),[4,8,12,16],[10],1373⟩,⟨227,(18),[3,4,7,8,12,15,16],[10],784⟩,⟨227,(19),[4,8,12,16],[10],1373⟩,⟨227,(20),[3,4,7,8,12,15,16],[10],785⟩,⟨227,(21),[3,4,7,8,12,15,16],[10],786⟩,⟨227,(22),[4,8,12,16],[10],1374⟩,⟨227,(23),[3,4,7,8,12,15,16],[10],788⟩,⟨227,(24),[4,8,12,16],[10],1374⟩,⟨228,(0),[3,4,8,12,15,16],[10],789⟩,⟨228,(1),[3,4,8,12,15,16],[10],790⟩,⟨228,(2),[4,8,12,16],[10],791⟩,⟨228,(3),[3,4,8,12,15,16],[10],792⟩,⟨228,(4),[3,4,7,8,12,15,16],[10],793⟩,⟨228,(5),[3,4,7,8,12,15,16],[10],794⟩,⟨228,(6),[3,4,7,8,12,15,16],[10],795⟩,⟨228,(7),[3,4,7,8,12,15,16],[10],796⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1440
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1441
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1442
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1443
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1444
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1445
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1446
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1447
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1448
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1449
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1450
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1451
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1452
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1453
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1454
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1455
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1456
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1457
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1458
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1459
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1460
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1461
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1462
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1463
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1464
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1465
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1466
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1467
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1468
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1469
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1470
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1471
end Section14Records_16_1440_1472

#print axioms solution
