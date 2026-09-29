-- Prove2me | solution 1 for Freiman.section14_s0008_records_1408_1440
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:27:26.268983+00:00
-- url     : https://prove2.me/submissions/a6b12be4-dc2a-457f-bbac-6154c0a95717

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
namespace Section14Records_8_1408_1440
private theorem valid1408 : RecordDataValid section14Catalog 8 (⟨200,(17),[3,4,8,12,15,16],[10],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1409 : RecordDataValid section14Catalog 8 (⟨200,(18),[3,4,8,12,15,16],[10],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1410 : RecordDataValid section14Catalog 8 (⟨200,(19),[3,4,8,12,15,16],[10],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1411 : RecordDataValid section14Catalog 8 (⟨200,(20),[3,4,8,12,15,16],[10],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1412 : RecordDataValid section14Catalog 8 (⟨200,(21),[3,4,8,12,15,16],[10],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1413 : RecordDataValid section14Catalog 8 (⟨200,(22),[3,4,8,12,15,16],[10],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1414 : RecordDataValid section14Catalog 8 (⟨200,(23),[3,4,8,12,15,16],[10],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1415 : RecordDataValid section14Catalog 8 (⟨200,(24),[3,4,8,12,15,16],[10],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1416 : RecordDataValid section14Catalog 8 (⟨202,(0),[4,8,12,16],[10],1329⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1329,[4,8,9,12,16],1333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1417 : RecordDataValid section14Catalog 8 (⟨202,(1),[4,8,12,16],[10],1330⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1330,[4,8,9,12,16],1334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1418 : RecordDataValid section14Catalog 8 (⟨202,(2),[4,8,12,16],[10],1329⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1329,[4,8,9,12,16],1333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1419 : RecordDataValid section14Catalog 8 (⟨202,(3),[4,8,12,16],[10],1331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1331,[4,8,9,12,16],1335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1420 : RecordDataValid section14Catalog 8 (⟨202,(4),[4,8,12,16],[10],1332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1332,[4,8,9,12,16],1336⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1421 : RecordDataValid section14Catalog 8 (⟨202,(5),[4,8,12,16],[10],1329⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1329,[4,8,9,12,16],1333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1422 : RecordDataValid section14Catalog 8 (⟨202,(6),[4,8,12,16],[10],1330⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1330,[4,8,9,12,16],1334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1423 : RecordDataValid section14Catalog 8 (⟨202,(7),[4,8,12,16],[10],1329⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1329,[4,8,9,12,16],1333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1424 : RecordDataValid section14Catalog 8 (⟨202,(8),[4,8,12,16],[10],1331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1331,[4,8,9,12,16],1335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1425 : RecordDataValid section14Catalog 8 (⟨202,(9),[4,8,12,16],[10],1332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1332,[4,8,9,12,16],1336⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1426 : RecordDataValid section14Catalog 8 (⟨202,(10),[4,8,12,16],[10],1333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1333,[4,8,9,12,16],1337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1427 : RecordDataValid section14Catalog 8 (⟨202,(11),[4,8,12,16],[10],1333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1333,[4,8,9,12,16],1337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1428 : RecordDataValid section14Catalog 8 (⟨202,(12),[4,8,12,16],[10],1333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1333,[4,8,9,12,16],1337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1429 : RecordDataValid section14Catalog 8 (⟨202,(13),[4,8,12,16],[10],1333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1333,[4,8,9,12,16],1337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1430 : RecordDataValid section14Catalog 8 (⟨202,(14),[4,8,12,16],[10],1332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1332,[4,8,9,12,16],1336⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1431 : RecordDataValid section14Catalog 8 (⟨202,(15),[4,8,12,16],[10],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1432 : RecordDataValid section14Catalog 8 (⟨202,(16),[4,8,12,16],[10],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1433 : RecordDataValid section14Catalog 8 (⟨202,(17),[4,8,12,16],[10],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1434 : RecordDataValid section14Catalog 8 (⟨202,(18),[4,8,12,16],[10],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1435 : RecordDataValid section14Catalog 8 (⟨202,(19),[4,8,12,16],[10],1334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1334,[4,8,9,12,16],1338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1436 : RecordDataValid section14Catalog 8 (⟨202,(20),[4,8,12,16],[10],1335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1335,[4,8,9,12,16],1339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1437 : RecordDataValid section14Catalog 8 (⟨202,(21),[4,8,12,16],[10],1335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1335,[4,8,9,12,16],1339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1438 : RecordDataValid section14Catalog 8 (⟨202,(22),[4,8,12,16],[10],1335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1335,[4,8,9,12,16],1339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1439 : RecordDataValid section14Catalog 8 (⟨202,(23),[4,8,12,16],[10],1335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1335,[4,8,9,12,16],1339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1408).take 32 = [⟨200,(17),[3,4,8,12,15,16],[10],710⟩,⟨200,(18),[3,4,8,12,15,16],[10],710⟩,⟨200,(19),[3,4,8,12,15,16],[10],710⟩,⟨200,(20),[3,4,8,12,15,16],[10],706⟩,⟨200,(21),[3,4,8,12,15,16],[10],707⟩,⟨200,(22),[3,4,8,12,15,16],[10],708⟩,⟨200,(23),[3,4,8,12,15,16],[10],707⟩,⟨200,(24),[3,4,8,12,15,16],[10],709⟩,⟨202,(0),[4,8,12,16],[10],1329⟩,⟨202,(1),[4,8,12,16],[10],1330⟩,⟨202,(2),[4,8,12,16],[10],1329⟩,⟨202,(3),[4,8,12,16],[10],1331⟩,⟨202,(4),[4,8,12,16],[10],1332⟩,⟨202,(5),[4,8,12,16],[10],1329⟩,⟨202,(6),[4,8,12,16],[10],1330⟩,⟨202,(7),[4,8,12,16],[10],1329⟩,⟨202,(8),[4,8,12,16],[10],1331⟩,⟨202,(9),[4,8,12,16],[10],1332⟩,⟨202,(10),[4,8,12,16],[10],1333⟩,⟨202,(11),[4,8,12,16],[10],1333⟩,⟨202,(12),[4,8,12,16],[10],1333⟩,⟨202,(13),[4,8,12,16],[10],1333⟩,⟨202,(14),[4,8,12,16],[10],1332⟩,⟨202,(15),[4,8,12,16],[10],1334⟩,⟨202,(16),[4,8,12,16],[10],1334⟩,⟨202,(17),[4,8,12,16],[10],1334⟩,⟨202,(18),[4,8,12,16],[10],1334⟩,⟨202,(19),[4,8,12,16],[10],1334⟩,⟨202,(20),[4,8,12,16],[10],1335⟩,⟨202,(21),[4,8,12,16],[10],1335⟩,⟨202,(22),[4,8,12,16],[10],1335⟩,⟨202,(23),[4,8,12,16],[10],1335⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1408
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1409
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1410
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1411
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1412
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1413
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1414
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1415
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1416
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1417
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1418
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1419
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1420
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1421
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1422
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1423
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1424
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1425
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1426
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1427
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1428
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1429
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1430
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1431
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1432
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1433
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1434
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1435
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1436
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1437
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1438
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1439
end Section14Records_8_1408_1440

#print axioms solution
