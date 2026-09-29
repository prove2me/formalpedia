-- Prove2me | solution 1 for Freiman.section14_s0015_records_1600_1632
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:30:31.692443+00:00
-- url     : https://prove2.me/submissions/00cb4d97-6ceb-41b1-b11e-b395bc9348f9

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
namespace Section14Records_15_1600_1632
private theorem valid1600 : RecordDataValid section14Catalog 15 (⟨470,(8),[3,7,15],[10],1219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1219,[3,7,11,15],1223⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1601 : RecordDataValid section14Catalog 15 (⟨470,(9),[3,7,15],[10],1220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1220,[3,7,11,15],1224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1602 : RecordDataValid section14Catalog 15 (⟨470,(10),[3,7,15],[10],1221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1221,[3,7,11,15],1225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1603 : RecordDataValid section14Catalog 15 (⟨470,(11),[3,7,15],[10],1222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1222,[3,7,11,15],1226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1604 : RecordDataValid section14Catalog 15 (⟨470,(12),[3,7,15],[10],1223⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1223,[3,7,11,15],1227⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1605 : RecordDataValid section14Catalog 15 (⟨470,(13),[3,7,15],[10],1220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1220,[3,7,11,15],1224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1606 : RecordDataValid section14Catalog 15 (⟨470,(14),[3,7,15],[10],1221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1221,[3,7,11,15],1225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1607 : RecordDataValid section14Catalog 15 (⟨470,(15),[3,7,15],[10],1222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1222,[3,7,11,15],1226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1608 : RecordDataValid section14Catalog 15 (⟨471,(0),[3,7,15],[10],1224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1224,[3,7,11,15],1228⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1609 : RecordDataValid section14Catalog 15 (⟨471,(1),[3,7,15],[10],1224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1224,[3,7,11,15],1228⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1610 : RecordDataValid section14Catalog 15 (⟨471,(2),[3,7,15],[10],1225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1225,[3,7,11,15],1229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1611 : RecordDataValid section14Catalog 15 (⟨471,(3),[3,7,15],[10],1225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1225,[3,7,11,15],1229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1612 : RecordDataValid section14Catalog 15 (⟨471,(4),[3,7,15],[10],1226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1226,[3,7,11,15],1230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1613 : RecordDataValid section14Catalog 15 (⟨471,(5),[3,7,15],[10],1226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1226,[3,7,11,15],1230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1614 : RecordDataValid section14Catalog 15 (⟨471,(6),[3,7,15],[10],1227⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1227,[3,7,11,15],1231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1615 : RecordDataValid section14Catalog 15 (⟨471,(7),[3,7,15],[10],1227⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1227,[3,7,11,15],1231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1616 : RecordDataValid section14Catalog 15 (⟨472,(0),[3,7,15],[10],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1617 : RecordDataValid section14Catalog 15 (⟨472,(1),[3,7,15],[10],1229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1229,[3,5,7,8,9,11,12,15],1233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1618 : RecordDataValid section14Catalog 15 (⟨472,(2),[3,7,15],[10],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1619 : RecordDataValid section14Catalog 15 (⟨472,(3),[3,7,15],[10],1230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1230,[3,5,7,8,9,11,12,15],1234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1620 : RecordDataValid section14Catalog 15 (⟨472,(4),[3,7,15],[10],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1621 : RecordDataValid section14Catalog 15 (⟨472,(5),[3,7,15],[10],1232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1232,[3,5,7,8,9,11,12,15],1236⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1622 : RecordDataValid section14Catalog 15 (⟨472,(6),[3,7,15],[10],1233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1233,[3,7,11,15],1237⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1623 : RecordDataValid section14Catalog 15 (⟨472,(7),[3,7,15],[10],1234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1234,[3,7,11,15],1238⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1624 : RecordDataValid section14Catalog 15 (⟨472,(8),[3,7,15],[10],1235⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1235,[3,5,7,8,9,11,12,15],1239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1625 : RecordDataValid section14Catalog 15 (⟨472,(9),[3,7,15],[10],1236⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1236,[3,5,7,8,9,11,12,15],1240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1626 : RecordDataValid section14Catalog 15 (⟨472,(10),[3,7,15],[10],1237⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1237,[3,7,11,15],1241⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1627 : RecordDataValid section14Catalog 15 (⟨472,(11),[3,7,15],[10],1238⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1238,[3,7,11,15],1242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1628 : RecordDataValid section14Catalog 15 (⟨472,(12),[3,7,15],[10],1239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1239,[3,5,7,8,9,11,12,15],1243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1629 : RecordDataValid section14Catalog 15 (⟨472,(13),[3,7,15],[10],1240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1240,[3,5,7,8,9,11,12,15],1244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1630 : RecordDataValid section14Catalog 15 (⟨472,(14),[3,7,15],[10],1241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1241,[3,7,11,15],1245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1631 : RecordDataValid section14Catalog 15 (⟨472,(15),[3,7,15],[10],1241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1241,[3,7,11,15],1245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1600).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1600).take 32 = [⟨470,(8),[3,7,15],[10],1219⟩,⟨470,(9),[3,7,15],[10],1220⟩,⟨470,(10),[3,7,15],[10],1221⟩,⟨470,(11),[3,7,15],[10],1222⟩,⟨470,(12),[3,7,15],[10],1223⟩,⟨470,(13),[3,7,15],[10],1220⟩,⟨470,(14),[3,7,15],[10],1221⟩,⟨470,(15),[3,7,15],[10],1222⟩,⟨471,(0),[3,7,15],[10],1224⟩,⟨471,(1),[3,7,15],[10],1224⟩,⟨471,(2),[3,7,15],[10],1225⟩,⟨471,(3),[3,7,15],[10],1225⟩,⟨471,(4),[3,7,15],[10],1226⟩,⟨471,(5),[3,7,15],[10],1226⟩,⟨471,(6),[3,7,15],[10],1227⟩,⟨471,(7),[3,7,15],[10],1227⟩,⟨472,(0),[3,7,15],[10],1228⟩,⟨472,(1),[3,7,15],[10],1229⟩,⟨472,(2),[3,7,15],[10],1228⟩,⟨472,(3),[3,7,15],[10],1230⟩,⟨472,(4),[3,7,15],[10],1231⟩,⟨472,(5),[3,7,15],[10],1232⟩,⟨472,(6),[3,7,15],[10],1233⟩,⟨472,(7),[3,7,15],[10],1234⟩,⟨472,(8),[3,7,15],[10],1235⟩,⟨472,(9),[3,7,15],[10],1236⟩,⟨472,(10),[3,7,15],[10],1237⟩,⟨472,(11),[3,7,15],[10],1238⟩,⟨472,(12),[3,7,15],[10],1239⟩,⟨472,(13),[3,7,15],[10],1240⟩,⟨472,(14),[3,7,15],[10],1241⟩,⟨472,(15),[3,7,15],[10],1241⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1600
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1601
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1602
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1603
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1604
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1605
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1606
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1607
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1608
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1609
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1610
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1611
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1612
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1613
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1614
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1615
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1616
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1617
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1618
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1619
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1620
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1621
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1622
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1623
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1624
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1625
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1626
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1627
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1628
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1629
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1630
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1631
end Section14Records_15_1600_1632

#print axioms solution
