-- Prove2me | solution 1 for Freiman.section14_s0012_records_1504_1536
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:59:44.684362+00:00
-- url     : https://prove2.me/submissions/c86e98fd-3366-4441-b936-0d68e9abd72c

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
namespace Section14Records_12_1504_1536
private theorem valid1504 : RecordDataValid section14Catalog 12 (⟨224,(18),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1505 : RecordDataValid section14Catalog 12 (⟨224,(19),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1506 : RecordDataValid section14Catalog 12 (⟨224,(20),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1507 : RecordDataValid section14Catalog 12 (⟨224,(21),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1508 : RecordDataValid section14Catalog 12 (⟨224,(22),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1509 : RecordDataValid section14Catalog 12 (⟨224,(23),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1510 : RecordDataValid section14Catalog 12 (⟨224,(24),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1511 : RecordDataValid section14Catalog 12 (⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1512 : RecordDataValid section14Catalog 12 (⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1513 : RecordDataValid section14Catalog 12 (⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1514 : RecordDataValid section14Catalog 12 (⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1515 : RecordDataValid section14Catalog 12 (⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1516 : RecordDataValid section14Catalog 12 (⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1517 : RecordDataValid section14Catalog 12 (⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1518 : RecordDataValid section14Catalog 12 (⟨225,(7),[4,8,12,16],[10],1368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1368,[4,8,9,12,16],1372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1519 : RecordDataValid section14Catalog 12 (⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1520 : RecordDataValid section14Catalog 12 (⟨225,(9),[4,8,12,16],[10],1368⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1368,[4,8,9,12,16],1372⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1521 : RecordDataValid section14Catalog 12 (⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1522 : RecordDataValid section14Catalog 12 (⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1523 : RecordDataValid section14Catalog 12 (⟨225,(12),[4,8,12,16],[10],1369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1369,[4,8,9,12,16],1373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1524 : RecordDataValid section14Catalog 12 (⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1525 : RecordDataValid section14Catalog 12 (⟨225,(14),[4,8,12,16],[10],1369⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1369,[4,8,9,12,16],1373⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1526 : RecordDataValid section14Catalog 12 (⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1527 : RecordDataValid section14Catalog 12 (⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1528 : RecordDataValid section14Catalog 12 (⟨225,(17),[4,8,12,16],[10],1370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1370,[4,8,9,12,16],1374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1529 : RecordDataValid section14Catalog 12 (⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1530 : RecordDataValid section14Catalog 12 (⟨225,(19),[4,8,12,16],[10],1370⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1370,[4,8,9,12,16],1374⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1531 : RecordDataValid section14Catalog 12 (⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1532 : RecordDataValid section14Catalog 12 (⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1533 : RecordDataValid section14Catalog 12 (⟨225,(22),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1534 : RecordDataValid section14Catalog 12 (⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1535 : RecordDataValid section14Catalog 12 (⟨225,(24),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1504).take 32 = [⟨224,(18),[4,8,12,16],[10],1355⟩,⟨224,(19),[4,8,12,16],[10],1356⟩,⟨224,(20),[4,8,12,16],[10],1367⟩,⟨224,(21),[4,8,12,16],[10],1367⟩,⟨224,(22),[4,8,12,16],[10],1367⟩,⟨224,(23),[4,8,12,16],[10],1355⟩,⟨224,(24),[4,8,12,16],[10],1356⟩,⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩,⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩,⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩,⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩,⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩,⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩,⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩,⟨225,(7),[4,8,12,16],[10],1368⟩,⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩,⟨225,(9),[4,8,12,16],[10],1368⟩,⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩,⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩,⟨225,(12),[4,8,12,16],[10],1369⟩,⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩,⟨225,(14),[4,8,12,16],[10],1369⟩,⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩,⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩,⟨225,(17),[4,8,12,16],[10],1370⟩,⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩,⟨225,(19),[4,8,12,16],[10],1370⟩,⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩,⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩,⟨225,(22),[4,8,12,16],[10],1367⟩,⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩,⟨225,(24),[4,8,12,16],[10],1367⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1504
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1505
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1506
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1507
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1508
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1509
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1510
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1511
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1512
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1513
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1514
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1515
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1516
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1517
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1518
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1519
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1520
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1521
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1522
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1523
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1524
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1525
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1526
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1527
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1528
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1529
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1530
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1531
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1532
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1533
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1534
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1535
end Section14Records_12_1504_1536

#print axioms solution
