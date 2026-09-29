-- Prove2me | solution 1 for Freiman.section14_s0015_records_1536_1568
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:27:36.354527+00:00
-- url     : https://prove2.me/submissions/092a5ae3-cf91-455d-89d3-4e64c755d838

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
namespace Section14Records_15_1536_1568
private theorem valid1536 : RecordDataValid section14Catalog 15 (⟨453,(2),[3,7,15],[10],1170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1170,[3,7,11,15],1174⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1537 : RecordDataValid section14Catalog 15 (⟨453,(3),[3,7,15],[10],1172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1172,[3,7,11,15],1176⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1538 : RecordDataValid section14Catalog 15 (⟨453,(4),[3,7,15],[10],1173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1173,[3,7,11,15],1177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1539 : RecordDataValid section14Catalog 15 (⟨453,(5),[3,7,15],[10],1173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1173,[3,7,11,15],1177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1540 : RecordDataValid section14Catalog 15 (⟨453,(6),[3,15],[10],1174⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1174,[3,15],1178⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1541 : RecordDataValid section14Catalog 15 (⟨453,(7),[3,7,15],[10],1173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1173,[3,7,11,15],1177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1542 : RecordDataValid section14Catalog 15 (⟨453,(8),[3,7,15],[10],1175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1175,[3,7,11,15],1179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1543 : RecordDataValid section14Catalog 15 (⟨453,(9),[3,7,15],[10],1175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1175,[3,7,11,15],1179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1544 : RecordDataValid section14Catalog 15 (⟨453,(10),[3,7,15],[10],1175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1175,[3,7,11,15],1179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1545 : RecordDataValid section14Catalog 15 (⟨453,(11),[3,7,15],[10],1175⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1175,[3,7,11,15],1179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1546 : RecordDataValid section14Catalog 15 (⟨453,(12),[3,7,15],[10],1176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1176,[3,7,11,15],1180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1547 : RecordDataValid section14Catalog 15 (⟨453,(13),[3,7,15],[10],1176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1176,[3,7,11,15],1180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1548 : RecordDataValid section14Catalog 15 (⟨453,(14),[3,7,15],[10],1176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1176,[3,7,11,15],1180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1549 : RecordDataValid section14Catalog 15 (⟨453,(15),[3,7,15],[10],1176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1176,[3,7,11,15],1180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1550 : RecordDataValid section14Catalog 15 (⟨460,(0),[3,7,15],[10],1184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1184,[3,7,11,15],1188⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1551 : RecordDataValid section14Catalog 15 (⟨460,(1),[3,7,15],[10],958⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨958,[3,7,11,15],962⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1552 : RecordDataValid section14Catalog 15 (⟨460,(2),[3,7,15],[10],959⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨959,[3,7,11,15],963⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1553 : RecordDataValid section14Catalog 15 (⟨460,(3),[3,7,15],[10],960⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨960,[3,7,11,15],964⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1554 : RecordDataValid section14Catalog 15 (⟨460,(4),[3,7,15],[10],961⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨961,[3,7,11,15],965⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1555 : RecordDataValid section14Catalog 15 (⟨461,(8),[3,7,15],[10],1185⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1185,[3,7,11,15],1189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1556 : RecordDataValid section14Catalog 15 (⟨461,(9),[3,7,15],[10],1186⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1186,[3,7,11,15],1190⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1557 : RecordDataValid section14Catalog 15 (⟨461,(10),[3,7,15],[10],1185⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1185,[3,7,11,15],1189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1558 : RecordDataValid section14Catalog 15 (⟨461,(11),[3,7,15],[10],1187⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1187,[3,7,11,15],1191⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1559 : RecordDataValid section14Catalog 15 (⟨462,(0),[3,7,15],[10],1188⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1188,[3,5,7,8,9,11,12,15],1192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1560 : RecordDataValid section14Catalog 15 (⟨462,(1),[3,7,15],[10],1189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1189,[3,5,7,8,9,11,12,15],1193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1561 : RecordDataValid section14Catalog 15 (⟨462,(2),[3,7,15],[10],1190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1190,[3,5,7,8,9,11,12,15],1194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1562 : RecordDataValid section14Catalog 15 (⟨462,(3),[3,7,15],[10],1191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1191,[3,5,7,8,9,11,12,15],1195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1563 : RecordDataValid section14Catalog 15 (⟨462,(4),[3,7,15],[10],1192⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1192,[3,7,8,11,12,15],1196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1564 : RecordDataValid section14Catalog 15 (⟨464,(0),[3,7,15],[10],1193⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1193,[3,7,11,15],1197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1565 : RecordDataValid section14Catalog 15 (⟨464,(1),[3,7,15],[10],1194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1194,[3,7,11,15],1198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1566 : RecordDataValid section14Catalog 15 (⟨464,(2),[3,7,15],[10],1195⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1195,[3,7,11,15],1199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1567 : RecordDataValid section14Catalog 15 (⟨464,(3),[3,7,15],[10],1196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1196,[3,7,11,15],1200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1536).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1536).take 32 = [⟨453,(2),[3,7,15],[10],1170⟩,⟨453,(3),[3,7,15],[10],1172⟩,⟨453,(4),[3,7,15],[10],1173⟩,⟨453,(5),[3,7,15],[10],1173⟩,⟨453,(6),[3,15],[10],1174⟩,⟨453,(7),[3,7,15],[10],1173⟩,⟨453,(8),[3,7,15],[10],1175⟩,⟨453,(9),[3,7,15],[10],1175⟩,⟨453,(10),[3,7,15],[10],1175⟩,⟨453,(11),[3,7,15],[10],1175⟩,⟨453,(12),[3,7,15],[10],1176⟩,⟨453,(13),[3,7,15],[10],1176⟩,⟨453,(14),[3,7,15],[10],1176⟩,⟨453,(15),[3,7,15],[10],1176⟩,⟨460,(0),[3,7,15],[10],1184⟩,⟨460,(1),[3,7,15],[10],958⟩,⟨460,(2),[3,7,15],[10],959⟩,⟨460,(3),[3,7,15],[10],960⟩,⟨460,(4),[3,7,15],[10],961⟩,⟨461,(8),[3,7,15],[10],1185⟩,⟨461,(9),[3,7,15],[10],1186⟩,⟨461,(10),[3,7,15],[10],1185⟩,⟨461,(11),[3,7,15],[10],1187⟩,⟨462,(0),[3,7,15],[10],1188⟩,⟨462,(1),[3,7,15],[10],1189⟩,⟨462,(2),[3,7,15],[10],1190⟩,⟨462,(3),[3,7,15],[10],1191⟩,⟨462,(4),[3,7,15],[10],1192⟩,⟨464,(0),[3,7,15],[10],1193⟩,⟨464,(1),[3,7,15],[10],1194⟩,⟨464,(2),[3,7,15],[10],1195⟩,⟨464,(3),[3,7,15],[10],1196⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1536
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1537
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1538
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1539
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1540
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1541
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1542
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1543
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1544
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1545
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1546
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1547
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1548
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1549
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1550
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1551
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1552
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1553
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1554
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1555
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1556
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1557
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1558
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1559
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1560
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1561
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1562
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1563
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1564
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1565
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1566
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1567
end Section14Records_15_1536_1568

#print axioms solution
