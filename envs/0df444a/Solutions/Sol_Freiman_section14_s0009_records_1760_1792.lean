-- Prove2me | solution 1 for Freiman.section14_s0009_records_1760_1792
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:58:38.589574+00:00
-- url     : https://prove2.me/submissions/fce3d137-3ed3-441b-a32b-74014a3ca672

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
namespace Section14Records_9_1760_1792
private theorem valid1760 : RecordDataValid section14Catalog 9 (⟨190,(5),[9,10],[42],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1761 : RecordDataValid section14Catalog 9 (⟨190,(6),[9,10],[42],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1762 : RecordDataValid section14Catalog 9 (⟨190,(7),[9,10],[42],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1763 : RecordDataValid section14Catalog 9 (⟨190,(8),[9,10],[42],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1764 : RecordDataValid section14Catalog 9 (⟨190,(9),[9,10],[42],691⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨691,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],692⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1765 : RecordDataValid section14Catalog 9 (⟨190,(10),[9,10],[42],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1766 : RecordDataValid section14Catalog 9 (⟨190,(11),[9,10],[42],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1767 : RecordDataValid section14Catalog 9 (⟨190,(12),[9,10],[42],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1768 : RecordDataValid section14Catalog 9 (⟨190,(13),[9,10],[42],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1769 : RecordDataValid section14Catalog 9 (⟨190,(14),[9,10],[42],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1770 : RecordDataValid section14Catalog 9 (⟨190,(15),[9,10],[42],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1771 : RecordDataValid section14Catalog 9 (⟨190,(16),[9,10],[42],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1772 : RecordDataValid section14Catalog 9 (⟨190,(17),[9,10],[42],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1773 : RecordDataValid section14Catalog 9 (⟨190,(18),[9,10],[42],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1774 : RecordDataValid section14Catalog 9 (⟨190,(19),[9,10],[42],696⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨696,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],697⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1775 : RecordDataValid section14Catalog 9 (⟨190,(20),[9,10],[42],692⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨692,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],693⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1776 : RecordDataValid section14Catalog 9 (⟨190,(21),[9,10],[42],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1777 : RecordDataValid section14Catalog 9 (⟨190,(22),[9,10],[42],694⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨694,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],695⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1778 : RecordDataValid section14Catalog 9 (⟨190,(23),[9,10],[42],693⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨693,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],694⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1779 : RecordDataValid section14Catalog 9 (⟨190,(24),[9,10],[42],695⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨695,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],696⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1780 : RecordDataValid section14Catalog 9 (⟨192,(0),[9],[42],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1781 : RecordDataValid section14Catalog 9 (⟨192,(1),[9],[42],1316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1316,[4,8,9,12,16],1320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1782 : RecordDataValid section14Catalog 9 (⟨192,(2),[9],[42],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1783 : RecordDataValid section14Catalog 9 (⟨192,(3),[9],[42],1317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1317,[4,8,9,12,16],1321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1784 : RecordDataValid section14Catalog 9 (⟨192,(4),[9],[42],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1785 : RecordDataValid section14Catalog 9 (⟨192,(5),[9],[42],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1786 : RecordDataValid section14Catalog 9 (⟨192,(6),[9],[42],1316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1316,[4,8,9,12,16],1320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1787 : RecordDataValid section14Catalog 9 (⟨192,(7),[9],[42],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1788 : RecordDataValid section14Catalog 9 (⟨192,(8),[9],[42],1317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1317,[4,8,9,12,16],1321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1789 : RecordDataValid section14Catalog 9 (⟨192,(9),[9],[42],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1790 : RecordDataValid section14Catalog 9 (⟨192,(10),[9],[42],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1791 : RecordDataValid section14Catalog 9 (⟨192,(11),[9],[42],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1760).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1760).take 32 = [⟨190,(5),[9,10],[42],691⟩,⟨190,(6),[9,10],[42],691⟩,⟨190,(7),[9,10],[42],691⟩,⟨190,(8),[9,10],[42],691⟩,⟨190,(9),[9,10],[42],691⟩,⟨190,(10),[9,10],[42],692⟩,⟨190,(11),[9,10],[42],693⟩,⟨190,(12),[9,10],[42],694⟩,⟨190,(13),[9,10],[42],693⟩,⟨190,(14),[9,10],[42],695⟩,⟨190,(15),[9,10],[42],692⟩,⟨190,(16),[9,10],[42],696⟩,⟨190,(17),[9,10],[42],696⟩,⟨190,(18),[9,10],[42],696⟩,⟨190,(19),[9,10],[42],696⟩,⟨190,(20),[9,10],[42],692⟩,⟨190,(21),[9,10],[42],693⟩,⟨190,(22),[9,10],[42],694⟩,⟨190,(23),[9,10],[42],693⟩,⟨190,(24),[9,10],[42],695⟩,⟨192,(0),[9],[42],1315⟩,⟨192,(1),[9],[42],1316⟩,⟨192,(2),[9],[42],1315⟩,⟨192,(3),[9],[42],1317⟩,⟨192,(4),[9],[42],1318⟩,⟨192,(5),[9],[42],1315⟩,⟨192,(6),[9],[42],1316⟩,⟨192,(7),[9],[42],1315⟩,⟨192,(8),[9],[42],1317⟩,⟨192,(9),[9],[42],1318⟩,⟨192,(10),[9],[42],1319⟩,⟨192,(11),[9],[42],1319⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1760
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1761
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1762
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1763
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1764
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1765
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1766
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1767
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1768
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1769
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1770
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1771
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1772
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1773
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1774
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1775
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1776
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1777
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1778
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1779
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1780
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1781
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1782
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1783
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1784
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1785
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1786
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1787
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1788
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1789
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1790
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1791
end Section14Records_9_1760_1792

#print axioms solution
