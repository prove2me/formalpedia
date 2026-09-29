-- Prove2me | solution 1 for Freiman.section14_s0008_records_1504_1536
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:29:42.67471+00:00
-- url     : https://prove2.me/submissions/fde55e2b-4bb2-4e76-95eb-2cf823204d89

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
namespace Section14Records_8_1504_1536
private theorem valid1504 : RecordDataValid section14Catalog 8 (⟨210,(13),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1505 : RecordDataValid section14Catalog 8 (⟨210,(14),[4,8,12,16],[10],727⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨727,[1,2,4,5,6,8,9,10,12,13,14,16],728⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1506 : RecordDataValid section14Catalog 8 (⟨210,(15),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1507 : RecordDataValid section14Catalog 8 (⟨213,(0),[4,8,12,16],[10],1343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1343,[4,8,9,12,16],1347⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1508 : RecordDataValid section14Catalog 8 (⟨213,(1),[4,8,12,16],[10],1344⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1344,[4,8,9,12,16],1348⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1509 : RecordDataValid section14Catalog 8 (⟨213,(2),[4,8,12,16],[10],1343⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1343,[4,8,9,12,16],1347⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1510 : RecordDataValid section14Catalog 8 (⟨213,(3),[4,8,12,16],[10],1345⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1345,[4,8,9,12,16],1349⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1511 : RecordDataValid section14Catalog 8 (⟨213,(4),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1512 : RecordDataValid section14Catalog 8 (⟨213,(5),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1513 : RecordDataValid section14Catalog 8 (⟨213,(6),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1514 : RecordDataValid section14Catalog 8 (⟨213,(7),[4,8,12,16],[10],1346⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1346,[4,8,9,12,16],1350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1515 : RecordDataValid section14Catalog 8 (⟨213,(8),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1516 : RecordDataValid section14Catalog 8 (⟨213,(9),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1517 : RecordDataValid section14Catalog 8 (⟨213,(10),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1518 : RecordDataValid section14Catalog 8 (⟨213,(11),[4,8,12,16],[10],1347⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1347,[4,8,9,12,16],1351⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1519 : RecordDataValid section14Catalog 8 (⟨213,(12),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1520 : RecordDataValid section14Catalog 8 (⟨213,(13),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1521 : RecordDataValid section14Catalog 8 (⟨213,(14),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1522 : RecordDataValid section14Catalog 8 (⟨213,(15),[4,8,12,16],[10],1348⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1348,[4,8,9,12,16],1352⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1523 : RecordDataValid section14Catalog 8 (⟨215,(0),[4,8,12],[10],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1524 : RecordDataValid section14Catalog 8 (⟨215,(1),[4,8,12],[10],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1525 : RecordDataValid section14Catalog 8 (⟨215,(2),[4,8,12],[10],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1526 : RecordDataValid section14Catalog 8 (⟨215,(3),[4,8,12],[10],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1527 : RecordDataValid section14Catalog 8 (⟨215,(4),[4,8,12],[10],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1528 : RecordDataValid section14Catalog 8 (⟨215,(5),[4,8,12],[10],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1529 : RecordDataValid section14Catalog 8 (⟨215,(6),[4,8,12],[10],732⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨732,[1,2,4,5,6,8,9,10,12],733⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1530 : RecordDataValid section14Catalog 8 (⟨215,(7),[4,8,12],[10],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1531 : RecordDataValid section14Catalog 8 (⟨215,(8),[4,8,12],[10],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1532 : RecordDataValid section14Catalog 8 (⟨215,(9),[4,8,12],[10],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1533 : RecordDataValid section14Catalog 8 (⟨215,(10),[4,8,12],[10],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1534 : RecordDataValid section14Catalog 8 (⟨215,(11),[4,8,12],[10],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1535 : RecordDataValid section14Catalog 8 (⟨215,(12),[4,8,12],[10],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1504).take 32 = [⟨210,(13),[4,8,12,16],[10],723⟩,⟨210,(14),[4,8,12,16],[10],727⟩,⟨210,(15),[4,8,12,16],[10],725⟩,⟨213,(0),[4,8,12,16],[10],1343⟩,⟨213,(1),[4,8,12,16],[10],1344⟩,⟨213,(2),[4,8,12,16],[10],1343⟩,⟨213,(3),[4,8,12,16],[10],1345⟩,⟨213,(4),[4,8,12,16],[10],1346⟩,⟨213,(5),[4,8,12,16],[10],1346⟩,⟨213,(6),[4,8,12,16],[10],1346⟩,⟨213,(7),[4,8,12,16],[10],1346⟩,⟨213,(8),[4,8,12,16],[10],1347⟩,⟨213,(9),[4,8,12,16],[10],1347⟩,⟨213,(10),[4,8,12,16],[10],1347⟩,⟨213,(11),[4,8,12,16],[10],1347⟩,⟨213,(12),[4,8,12,16],[10],1348⟩,⟨213,(13),[4,8,12,16],[10],1348⟩,⟨213,(14),[4,8,12,16],[10],1348⟩,⟨213,(15),[4,8,12,16],[10],1348⟩,⟨215,(0),[4,8,12],[10],728⟩,⟨215,(1),[4,8,12],[10],729⟩,⟨215,(2),[4,8,12],[10],730⟩,⟨215,(3),[4,8,12],[10],731⟩,⟨215,(4),[4,8,12],[10],728⟩,⟨215,(5),[4,8,12],[10],729⟩,⟨215,(6),[4,8,12],[10],732⟩,⟨215,(7),[4,8,12],[10],731⟩,⟨215,(8),[4,8,12],[10],728⟩,⟨215,(9),[4,8,12],[10],729⟩,⟨215,(10),[4,8,12],[10],730⟩,⟨215,(11),[4,8,12],[10],731⟩,⟨215,(12),[4,8,12],[10],728⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1504
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1505
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1506
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1507
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1508
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1509
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1510
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1511
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1512
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1513
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1514
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1515
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1516
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1517
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1518
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1519
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1520
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1521
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1522
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1523
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1524
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1525
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1526
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1527
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1528
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1529
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1530
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1531
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1532
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1533
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1534
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1535
end Section14Records_8_1504_1536

#print axioms solution
