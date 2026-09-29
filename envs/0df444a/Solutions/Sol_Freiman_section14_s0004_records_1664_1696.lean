-- Prove2me | solution 1 for Freiman.section14_s0004_records_1664_1696
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:49:45.70281+00:00
-- url     : https://prove2.me/submissions/b496e645-0d05-489e-9452-e70696dcce99

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
namespace Section14Records_4_1664_1696
private theorem valid1664 : RecordDataValid section14Catalog 4 (⟨222,(17),[3,4,7,15,16],[10],745⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨745,[1,2,3,4,5,6,7,10,11,13,14,15,16],746⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1665 : RecordDataValid section14Catalog 4 (⟨222,(18),[3,4,8,12,15,16],[10],746⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨746,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],747⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1666 : RecordDataValid section14Catalog 4 (⟨222,(19),[3,4,7,8,12,15,16],[10],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1667 : RecordDataValid section14Catalog 4 (⟨222,(20),[3,4,7,8,12,15,16],[10],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1668 : RecordDataValid section14Catalog 4 (⟨222,(21),[3,4,7,8,12,15,16],[10],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1669 : RecordDataValid section14Catalog 4 (⟨222,(22),[3,4,7,8,12,15,16],[10],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1670 : RecordDataValid section14Catalog 4 (⟨222,(23),[3,4,7,8,12,15,16],[10],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1671 : RecordDataValid section14Catalog 4 (⟨222,(24),[3,4,7,15,16],[10],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1672 : RecordDataValid section14Catalog 4 (⟨224,(0),[3,4,7,8,12,15,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1673 : RecordDataValid section14Catalog 4 (⟨224,(1),[3,4,7,8,12,15,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1674 : RecordDataValid section14Catalog 4 (⟨224,(2),[3,4,7,8,12,15,16],[10],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1675 : RecordDataValid section14Catalog 4 (⟨224,(3),[3,4,7,8,12,15,16],[10],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1676 : RecordDataValid section14Catalog 4 (⟨224,(4),[3,4,7,8,12,15,16],[10],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1677 : RecordDataValid section14Catalog 4 (⟨224,(5),[4,8,12,16],[10],1363⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1363,[4,8,9,12,16],1367⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1678 : RecordDataValid section14Catalog 4 (⟨224,(6),[4,8,12,16],[10],1363⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1363,[4,8,9,12,16],1367⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1679 : RecordDataValid section14Catalog 4 (⟨224,(7),[4,8,12,16],[10],1364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1364,[4,8,9,12,16],1368⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1680 : RecordDataValid section14Catalog 4 (⟨224,(8),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1681 : RecordDataValid section14Catalog 4 (⟨224,(9),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1682 : RecordDataValid section14Catalog 4 (⟨224,(10),[4,8,12,16],[10],1365⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1365,[4,8,9,12,16],1369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1683 : RecordDataValid section14Catalog 4 (⟨224,(11),[4,8,12,16],[10],1365⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1365,[4,8,9,12,16],1369⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1684 : RecordDataValid section14Catalog 4 (⟨224,(12),[4,8,12,16],[10],1364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1364,[4,8,9,12,16],1368⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1685 : RecordDataValid section14Catalog 4 (⟨224,(13),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1686 : RecordDataValid section14Catalog 4 (⟨224,(14),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1687 : RecordDataValid section14Catalog 4 (⟨224,(15),[4,8,12,16],[10],1366⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1366,[4,8,9,12,16],1370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1688 : RecordDataValid section14Catalog 4 (⟨224,(16),[4,8,12,16],[10],1366⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1366,[4,8,9,12,16],1370⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1689 : RecordDataValid section14Catalog 4 (⟨224,(17),[4,8,12,16],[10],1364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1364,[4,8,9,12,16],1368⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1690 : RecordDataValid section14Catalog 4 (⟨224,(18),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1691 : RecordDataValid section14Catalog 4 (⟨224,(19),[4,8,12,16],[10],1356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1356,[4,8,9,12,16],1360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1692 : RecordDataValid section14Catalog 4 (⟨224,(20),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1693 : RecordDataValid section14Catalog 4 (⟨224,(21),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1694 : RecordDataValid section14Catalog 4 (⟨224,(22),[4,8,12,16],[10],1367⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1367,[4,8,9,12,16],1371⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1695 : RecordDataValid section14Catalog 4 (⟨224,(23),[4,8,12,16],[10],1355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1355,[4,8,9,12,16],1359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1664).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 1664).take 32 = [⟨222,(17),[3,4,7,15,16],[10],745⟩,⟨222,(18),[3,4,8,12,15,16],[10],746⟩,⟨222,(19),[3,4,7,8,12,15,16],[10],534⟩,⟨222,(20),[3,4,7,8,12,15,16],[10],535⟩,⟨222,(21),[3,4,7,8,12,15,16],[10],536⟩,⟨222,(22),[3,4,7,8,12,15,16],[10],537⟩,⟨222,(23),[3,4,7,8,12,15,16],[10],538⟩,⟨222,(24),[3,4,7,15,16],[10],537⟩,⟨224,(0),[3,4,7,8,12,15,16],[10],539⟩,⟨224,(1),[3,4,7,8,12,15,16],[10],539⟩,⟨224,(2),[3,4,7,8,12,15,16],[10],540⟩,⟨224,(3),[3,4,7,8,12,15,16],[10],541⟩,⟨224,(4),[3,4,7,8,12,15,16],[10],542⟩,⟨224,(5),[4,8,12,16],[10],1363⟩,⟨224,(6),[4,8,12,16],[10],1363⟩,⟨224,(7),[4,8,12,16],[10],1364⟩,⟨224,(8),[4,8,12,16],[10],1355⟩,⟨224,(9),[4,8,12,16],[10],1356⟩,⟨224,(10),[4,8,12,16],[10],1365⟩,⟨224,(11),[4,8,12,16],[10],1365⟩,⟨224,(12),[4,8,12,16],[10],1364⟩,⟨224,(13),[4,8,12,16],[10],1355⟩,⟨224,(14),[4,8,12,16],[10],1356⟩,⟨224,(15),[4,8,12,16],[10],1366⟩,⟨224,(16),[4,8,12,16],[10],1366⟩,⟨224,(17),[4,8,12,16],[10],1364⟩,⟨224,(18),[4,8,12,16],[10],1355⟩,⟨224,(19),[4,8,12,16],[10],1356⟩,⟨224,(20),[4,8,12,16],[10],1367⟩,⟨224,(21),[4,8,12,16],[10],1367⟩,⟨224,(22),[4,8,12,16],[10],1367⟩,⟨224,(23),[4,8,12,16],[10],1355⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1664
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1665
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1666
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1667
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1668
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1669
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1670
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1671
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1672
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1673
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1674
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1675
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1676
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1677
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1678
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1679
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1680
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1681
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1682
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1683
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1684
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1685
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1686
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1687
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1688
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1689
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1690
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1691
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1692
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1693
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1694
  · exact recordValid_of_data section14Catalog 4 _ hnum valid1695
end Section14Records_4_1664_1696

#print axioms solution
