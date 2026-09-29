-- Prove2me | solution 1 for Freiman.section14_s0010_records_1440_1472
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T17:09:47.236051+00:00
-- url     : https://prove2.me/submissions/6ad448c8-5e40-46ad-868e-6f7c05cfa4cc

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
namespace Section14Records_10_1440_1472
private theorem valid1440 : RecordDataValid section14Catalog 10 (⟨142,(10),[9,10],[42],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1441 : RecordDataValid section14Catalog 10 (⟨142,(11),[9,10],[42],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1442 : RecordDataValid section14Catalog 10 (⟨142,(12),[9,10],[42],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1443 : RecordDataValid section14Catalog 10 (⟨142,(13),[9,10],[42],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1444 : RecordDataValid section14Catalog 10 (⟨142,(14),[9,10],[42],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1445 : RecordDataValid section14Catalog 10 (⟨142,(15),[9,10],[42],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1446 : RecordDataValid section14Catalog 10 (⟨143,(0),[9,10],[42],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1447 : RecordDataValid section14Catalog 10 (⟨143,(1),[9,10],[42],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1448 : RecordDataValid section14Catalog 10 (⟨143,(2),[9,10],[42],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1449 : RecordDataValid section14Catalog 10 (⟨143,(3),[9,10],[42],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1450 : RecordDataValid section14Catalog 10 (⟨143,(4),[9,10],[42],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1451 : RecordDataValid section14Catalog 10 (⟨143,(5),[9,10],[42],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1452 : RecordDataValid section14Catalog 10 (⟨143,(6),[9,10],[42],584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1453 : RecordDataValid section14Catalog 10 (⟨143,(7),[9,10],[42],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1454 : RecordDataValid section14Catalog 10 (⟨143,(8),[9,10],[42],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1455 : RecordDataValid section14Catalog 10 (⟨143,(9),[9,10],[42],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1456 : RecordDataValid section14Catalog 10 (⟨143,(10),[9,10],[42],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1457 : RecordDataValid section14Catalog 10 (⟨143,(11),[9,10],[42],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1458 : RecordDataValid section14Catalog 10 (⟨143,(12),[9,10],[42],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1459 : RecordDataValid section14Catalog 10 (⟨143,(13),[9,10],[42],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1460 : RecordDataValid section14Catalog 10 (⟨143,(14),[9,10],[42],588⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨588,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1461 : RecordDataValid section14Catalog 10 (⟨143,(15),[9,10],[42],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1462 : RecordDataValid section14Catalog 10 (⟨144,(0),[9,10],[42],590⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨590,[1,4,5,6,8,9,10,12,13,16],591⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1463 : RecordDataValid section14Catalog 10 (⟨144,(1),[9,10],[42],591⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨591,[1,4,5,6,8,9,10,12,13,16],592⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1464 : RecordDataValid section14Catalog 10 (⟨144,(2),[9,10],[42],590⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨590,[1,4,5,6,8,9,10,12,13,16],591⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1465 : RecordDataValid section14Catalog 10 (⟨144,(3),[9,10],[42],592⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨592,[1,4,5,6,8,9,10,12,13,16],593⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1466 : RecordDataValid section14Catalog 10 (⟨145,(0),[9,10],[42],593⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨593,[1,4,5,6,8,9,10,12,13,16],594⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1467 : RecordDataValid section14Catalog 10 (⟨145,(1),[9,10],[42],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1468 : RecordDataValid section14Catalog 10 (⟨145,(2),[9,10],[42],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1469 : RecordDataValid section14Catalog 10 (⟨145,(3),[10],[42],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1470 : RecordDataValid section14Catalog 10 (⟨145,(4),[9,10],[42],597⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨597,[1,4,5,6,8,9,10,12,13,16],598⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1471 : RecordDataValid section14Catalog 10 (⟨145,(5),[9,10],[42],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1440).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1440).take 32 = [⟨142,(10),[9,10],[42],575⟩,⟨142,(11),[9,10],[42],575⟩,⟨142,(12),[9,10],[42],576⟩,⟨142,(13),[9,10],[42],577⟩,⟨142,(14),[9,10],[42],577⟩,⟨142,(15),[9,10],[42],577⟩,⟨143,(0),[9,10],[42],578⟩,⟨143,(1),[9,10],[42],579⟩,⟨143,(2),[9,10],[42],580⟩,⟨143,(3),[9,10],[42],581⟩,⟨143,(4),[9,10],[42],582⟩,⟨143,(5),[9,10],[42],583⟩,⟨143,(6),[9,10],[42],584⟩,⟨143,(7),[9,10],[42],585⟩,⟨143,(8),[9,10],[42],578⟩,⟨143,(9),[9,10],[42],579⟩,⟨143,(10),[9,10],[42],580⟩,⟨143,(11),[9,10],[42],581⟩,⟨143,(12),[9,10],[42],586⟩,⟨143,(13),[9,10],[42],587⟩,⟨143,(14),[9,10],[42],588⟩,⟨143,(15),[9,10],[42],589⟩,⟨144,(0),[9,10],[42],590⟩,⟨144,(1),[9,10],[42],591⟩,⟨144,(2),[9,10],[42],590⟩,⟨144,(3),[9,10],[42],592⟩,⟨145,(0),[9,10],[42],593⟩,⟨145,(1),[9,10],[42],594⟩,⟨145,(2),[9,10],[42],595⟩,⟨145,(3),[10],[42],596⟩,⟨145,(4),[9,10],[42],597⟩,⟨145,(5),[9,10],[42],598⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1440
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1441
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1442
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1443
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1444
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1445
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1446
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1447
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1448
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1449
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1450
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1451
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1452
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1453
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1454
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1455
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1456
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1457
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1458
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1459
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1460
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1461
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1462
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1463
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1464
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1465
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1466
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1467
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1468
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1469
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1470
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1471
end Section14Records_10_1440_1472

#print axioms solution
